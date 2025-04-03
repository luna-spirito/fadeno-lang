module Normalize where

import Data.RRBVector (Vector, drop, viewl, (|>))
import GHC.Exts (IsList (..))
import Language.Haskell.TH.Quote (QuasiQuoter (..))
import Parser (BlockT (..), BuiltinT (..), Fields (..), Lambda (..), OpT (..), TermT (..), builtinsList, identOfBuiltin, pTerm', parseFile, parseQQ, recordGet, render)
import RIO hiding (Reader, Vector, ask, drop, link, local, replicate, runReader, to, toList)

-- class HasTerm m a where
--   extractTerm ∷ a → m TermT
--   mkFromTerm ∷ Proxy m → TermT → a

-- instance (Applicative m) ⇒ HasTerm m TermT where
--   extractTerm t = pure t
--   mkFromTerm _ = id

-- instance (Applicative m) ⇒ HasTerm m (Maybe TermT, TermT) where
--   extractTerm t = pure $ fst t
--   mkFromTerm _ = (,undefined) . Just

-- TODO: implement REWRITES, and implement ExVar substitution via REWRITES
-- NOTE: normalize shouldn't process both normalizations and rewrites at the same time.

-- | Intensional equality.
data EqRes
  = EqYes -- provably eq
  | EqNot -- provably uneq
  | EqUnknown

{- | Checks if two normalized terms are intensionally equivalent.
TODO: η-conversion
-}
isEq ∷ TermT → TermT → EqRes
isEq = curry \case
  (Block{}, _) → undefined
  (_, Block{}) → undefined
  (Var a, Var b)
    | a == b → EqYes
  (Var _, _) → EqUnknown
  (_, Var _) → EqUnknown
  (UniVar _ b1 _, UniVar _ b2 _)
    | b1 == b2 → EqYes
  (UniVar{}, _) → EqUnknown
  (_, UniVar{}) → EqUnknown
  -- TODO: ExVar? I don't know!
  (ExVar{}, _) → error "TODO"
  (_, ExVar{}) → error "TODO"
  (App f1 a1, App f2 a2) → tryEq f1 f2 $ tryEq a1 a2 $ EqYes
  (App{}, _) → EqUnknown
  (_, App{}) → EqUnknown
  (Op a1 op1 b1, Op a2 op2 b2)
    | op1 == op2 → tryEq a1 a2 $ tryEq b1 b2 $ EqYes
  (Op{}, _) → EqUnknown
  (_, Op{}) → EqUnknown
  (Sorry _ a, b) → isEq a b
  (a, Sorry _ b) → isEq a b
  -- Literals
  (Lam _ bod1, Lam _ bod2) → isEq (unLambda bod1) (unLambda bod2)
  (Lam _ _, _) → EqNot
  (NatLit a, NatLit b)
    | a == b → EqYes
  (NatLit _, _) → EqNot
  (TagLit a, TagLit b)
    | a == b → EqYes
  (TagLit _, _) → EqNot
  (Quantification q1 _n1 k1 t1, Quantification q2 _n2 k2 t2)
    | q1 == q2 → case isEq k1 k2 of
        EqYes → isEq (unLambda t1) (unLambda t2)
        x → x
  (Quantification{}, _) → EqUnknown
  (Builtin a, Builtin b)
    | a == b → EqYes
  (Builtin _, _) → EqNot
  (_, Builtin _) → EqNot
  (BuiltinsVar, BuiltinsVar) → EqYes
  (BuiltinsVar, _) → EqNot
  (_, BuiltinsVar) → EqNot
  -- TODO: Handle mixed?
  -- Shame.
  (Pi inT1 (Left (_, outT1)), Pi inT2 (Left (_, outT2))) →
    case isEq inT1 inT2 of
      EqYes → isEq (unLambda outT1) (unLambda outT2)
      x → x
  (Pi inT1 (Right outT1), Pi inT2 (Right outT2)) →
    case isEq inT1 inT2 of
      EqYes → isEq outT1 outT2
      x → x
  (Pi{}, _) → EqNot
  (FieldsLit _, _) → error "isEq Fields todo"
 where
  -- TODO: FRow???
  tryEq a b cont =
    case isEq a b of
      EqYes → cont
      _ → EqUnknown

data NormCtx
  = NormBinds !(Vector (Maybe TermT))
  | NormRewrite !TermT !TermT -- on normalized

-- Rewrites & simplifies. In that order. Doesn't rewrite the simplified result.
rewrite ∷ ∀ f via. (Monad f) ⇒ (TermT → via → via) → (via → via) → (TermT → via → f (Maybe TermT)) → via → TermT → f TermT
rewrite onLet onNest rewriter = go
 where
  go ∷ via → TermT → f TermT
  go via term =
    rewriter term via >>= \case
      Just res → pure res
      Nothing → go' via term

  go' ∷ via → TermT → f TermT
  go' via = \case
    Block (BlockLet _ _ val into) → do
      val' ← go via val
      go (onLet val' via) $ unLambda into
    Block (BlockRewrite from to) → error "TODO rewrite BlockRewrite"
    Lam arg bod → Lam arg . Lambda <$> go (onNest via) (unLambda bod)
    Op aT op bT → do
      aT' ← go via aT
      bT' ← go via bT
      pure $ case (aT', bT') of
        (NatLit a, NatLit b) → NatLit $ case op of
          Add → a + b
          Sub → a - b
          Mul → a * b
          Div → a `div` b
        _ → Op aT' op bT'
    App f a → do
      f' ← go via f
      a' ← go via a
      pure $ case f' of
        Lam _ bod → applyLambda bod a'
        App (Builtin RecordGet) name →
          let
            rec = a'
            search = \case
              FieldsLit (Right (Fields [] (Just rest))) → search rest
              FieldsLit (Right (Fields ((name2, val) : xs) rest))
                | name == name2 → val
                | otherwise → search $ FieldsLit (Right (Fields xs rest))
              x → recordGet name x
           in
            search rec
        _ → App f' a'
    NatLit x → pure $ NatLit x
    TagLit x → pure $ TagLit x
    FieldsLit fields →
      let withFields f = case fields of
            Left row → Left . Lambda <$> f (onNest via) (unLambda row)
            Right record → Right <$> f via record
       in FieldsLit <$> withFields \via' (Fields knownFields rest) →
            Fields
              <$> traverse (bitraverse (go via') (go via')) knownFields
              <*> traverse (go via') rest
    Sorry n x → Sorry n <$> go via x
    Var i → pure $ Var i
    Quantification q x a b → Quantification q x <$> go via a <*> (Lambda <$> go (onNest via) (unLambda b))
    Builtin x → pure $ Builtin x
    BuiltinsVar → pure BuiltinsVar
    Pi inT outT → do
      inT' ← go via inT
      outT' ← case outT of
        Left (n, x) → Left . (n,) . Lambda <$> go (onNest via) (unLambda x)
        Right x → Right <$> go via x
      pure $ Pi inT' outT'
    ExVar n i t → ExVar n i <$> traverse (go via) t
    UniVar n i t → UniVar n i <$> go via t

nestedBy ∷ Int → TermT → TermT
nestedBy by =
  runIdentity
    . rewrite
      (\_ → (+ 1))
      (+ 1)
      ( \term locs → case term of
          Var i | i >= locs → pure $ Just $ Var $ i + by
          _ → pure Nothing
      )
      0

nested ∷ TermT → TermT
nested = nestedBy 1

normalize ∷ Vector (Maybe TermT) → TermT → TermT
normalize origBinds =
  runIdentity
    . rewrite
      (\new old → (fmap nested <$> old) |> Just new)
      (\old → (fmap nested <$> old) |> Nothing)
      ( \term binds → case term of
          Var i →
            pure
              $ Just
              $ let after = drop (length binds - i - 1) binds
                 in case after of
                      (viewl → Just (Just val, _)) → val
                      _ → Var $ i - foldl' (\acc x → if isJust x then acc + 1 else acc) 0 after
          _ → pure Nothing
      )
      origBinds

rewriteTerm ∷ TermT → TermT → TermT → TermT
rewriteTerm what0 with0 =
  runIdentity
    . rewrite
      (const (bimap nested nested))
      (bimap nested nested)
      ( \term (what, with) → pure $ case isEq term what of
          EqYes → Just with
          _ → Nothing
      )
      (what0, with0)

applyLambda ∷ Lambda TermT → TermT → TermT
applyLambda bod val = normalize [Just val] $ unLambda bod

--  extractVar var = maybe (pure Nothing) extractTerm $ HM.lookup var binds

normalizeBuiltin ∷ TermT → TermT
normalizeBuiltin = normalize (Just . Builtin <$> fromList builtinsList)

-- | Parse builtin
parseBQQ ∷ QuasiQuoter
parseBQQ =
  QuasiQuoter
    { quoteExp = \s → ⟦normalizeBuiltin $(quoteExp (parseQQ $ identOfBuiltin <$> fromList builtinsList) s)⟧
    , quotePat = error "No pattern support"
    , quoteType = error "No type support"
    , quoteDec = error "No declaration support"
    }

normalizeFile ∷ FilePath → IO ()
normalizeFile x = do
  t ← parseFile x
  render $ pTerm' $ normalize [] t
