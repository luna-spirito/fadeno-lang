-- I REALLY don't like this module, but we've gotta do what we've gotta do I guess.
-- The plan is to eventually move this logic into Fadeno itself, I hope?
module Arithmetic where

import Data.Foldable1 (foldl1')
import Data.Functor.Classes (Ord1 (liftCompare))
import Data.RRBVector (Vector, viewl, viewr)
import GHC.IsList (IsList (..))
import Parser (BuiltinT (..), Fields (..), Lambda (..), NumDesc (..), Quant (..), Term (..), TermF (..), pattern Op2)
import RIO hiding (Vector, toList)

compareTerm ∷ Term → Term → Ordering
compareTerm = \(Term a) (Term b) →
  let rka = rank a
      rkb = rank b
   in case compare rka rkb of
        EQ → compareSame a b
        ord → ord
 where
  rank ∷ TermF t → Int
  rank = \case
    NumLit _ → 0
    TagLit _ → 1
    BoolLit _ → 2
    ListLit _ → 3
    FieldsLit _ _ → 4
    BuiltinsVar → undefined
    Builtin _ → 6
    Lam{} → 7
    App{} → 8
    Var{} → 9
    Sorry → 10
    AppErased{} → undefined
    Block{} → undefined
    Pi{} → 13
    Concat{} → 14
    ExVar{} → 15
    UniVar{} → 16
    Import{} → 17

  compareFields ∷ (x → x → Ordering) → (y → y → Ordering) → Fields x y → Fields x y → Ordering
  compareFields cmpX cmpY = curry \case
    (FRecord x1, FRecord x2) → cmpX x1 x2
    (FRecord _, FRow _) → LT
    (FRow _, FRecord _) → GT
    (FRow y1, FRow y2) → cmpY y1 y2

  compareSame ∷ TermF Term → TermF Term → Ordering
  compareSame = curry \case
    (Block _, _) → undefined
    (BuiltinsVar, _) → undefined
    (AppErased{}, _) → undefined
    (Lam QEra _ _, _) → undefined
    --
    (NumLit n1, NumLit n2) → compare n1 n2
    (NumLit _, _) → undefined
    (TagLit t1, TagLit t2) → compare t1 t2
    (TagLit _, _) → undefined
    (BoolLit a, BoolLit b) → compare a b
    (BoolLit _, _) → undefined
    (ListLit v1, ListLit v2) → liftCompare compareTerm v1 v2
    (ListLit _, _) → undefined
    (FieldsLit f1 pairs1, FieldsLit f2 pairs2) →
      compareFields (\() () → EQ) (\() () → EQ) f1 f2
        <> liftCompare (\(aL, bL) (aR, bR) → compareTerm aL aR <> compareTerm bL bR) pairs1 pairs2
    (FieldsLit _ _, _) → undefined
    (Builtin b1, Builtin b2) → compare b1 b2
    (Builtin _, _) → EQ
    (Lam QNorm _ body1, Lam QNorm _ body2) → compareTerm (unLambda body1) (unLambda body2)
    (Lam{}, _) → undefined
    (App f1 a1, App f2 a2) → compareTerm f1 f2 <> compareTerm a1 a2
    (App{}, _) → undefined
    (Var n1, Var n2) → compare n1 n2
    (Var _, _) → undefined
    (Import _ a, Import _ b) → compare a b
    (Import{}, _) → undefined
    (Sorry, Sorry) → EQ
    (Sorry, _) → undefined
    (Pi q1 _ inT1 outT1, Pi q2 _ inT2 outT2) →
      compare q1 q2 <> compareTerm inT1 inT2 <> compareTerm (unLambda outT1) (unLambda outT2)
    (Pi{}, _) → undefined
    (Concat t1 f1, Concat t2 f2) →
      compareTerm t1 t2
        <> compareFields compareTerm (\b1 b2 → compareTerm (unLambda b1) (unLambda b2)) f1 f2
    (Concat _ _, _) → undefined
    (ExVar (a1, b1), ExVar (a2, b2)) → compare a1 a2 <> compare b1 b2
    (ExVar{}, _) → undefined
    (UniVar (i1, j1) _, UniVar (i2, j2) _) → compare i1 i2 <> compare j1 j2
    (UniVar{}, _) → undefined

mergeSorted ∷ (a → a → Ordering) → [a] → [a] → [a]
mergeSorted f = curry \case
  (xs, []) → xs
  ([], xs) → xs
  (xs@(x : xt), ys@(y : yt)) →
    case f x y of
      GT → y : mergeSorted f xs yt
      _ → x : mergeSorted f xt ys

data DupPoly = DupPoly !(Vector (Integer, Term)) !Integer
  deriving (Show, Eq)

instance Semigroup DupPoly where
  DupPoly as ac <> DupPoly bs bc = DupPoly merged (ac + bc)
   where
    merged
      | Just LT ← (\(_, (_, a)) ((_, b), _) → compareTerm a b) <$> viewr as <*> viewl bs = as <> bs
      | otherwise = fromList $ mergeSorted (\(_, a) (_, b) → compareTerm a b) (toList as) (toList bs)

mulDupPoly ∷ DupPoly → DupPoly → DupPoly
mulDupPoly (DupPoly as ac) (DupPoly bs bc) =
  let poly = (`DupPoly` 0)
   in poly ((\(c1, t1) (c2, t2) → (c1 * c2, Term $ Op2 (Mul NumInf) t1 t2)) <$> as <*> bs) -- as * bs
        <> poly (first (* bc) <$> as) -- as * bc
        <> poly (first (* ac) <$> bs) -- ac * bs
        <> DupPoly [] (ac * bc)

termToDupPoly ∷ Term → DupPoly
termToDupPoly =
  unTerm >>> \case
    NumLit n → DupPoly [] n
    Op2 (Add NumInf) a b → termToDupPoly a <> termToDupPoly b
    Op2 (Mul NumInf) a b → termToDupPoly a `mulDupPoly` termToDupPoly b
    (unTerm → Builtin (IntNeg NumInf)) `App` a → (\(DupPoly ress resc) → DupPoly (first (\x → -x) <$> ress) (-resc)) $ termToDupPoly a
    x → DupPoly [(1, Term x)] 0

dupPolyToTerm ∷ DupPoly → Term
dupPolyToTerm = \(DupPoly origXs origXc) → case toTerm =<< dedupPoly (toList origXs) of
  (x : xs) →
    let polyPart = foldl1' (\a b → Term $ Op2 (Add NumInf) a b) (x :| xs)
     in if origXc == 0
          then polyPart
          else Term $ Op2 (Add NumInf) polyPart $ Term $ NumLit origXc
  _ → Term $ NumLit origXc
 where
  toTerm = \case
    (0, _) → []
    (1, x) → [x]
    (n, x) → [Term $ Op2 (Mul NumInf) (Term $ NumLit n) x]
  dedupPoly = \case
    (a : b : xs)
      | EQ ← compareTerm (snd a) (snd b) → dedupPoly $ (fst a + fst b, snd a) : xs
      | otherwise → a : dedupPoly (b : xs)
    final → final

normalizePoly ∷ Term → Term
normalizePoly = dupPolyToTerm . termToDupPoly
