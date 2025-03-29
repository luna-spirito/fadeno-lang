module Normalize where

import Control.Algebra
import Control.Effect.Lift (Lift, sendIO)
import Data.RRBVector (Vector, drop, replicate, splitAt, viewl, (|>))
import GHC.Exts (IsList (..))
import Language.Haskell.TH.Quote (QuasiQuoter (..))
import Parser (BlockT (..), BuiltinT (..), Fields (..), Lambda (..), OpT (..), TermT (..), builtinsList, identOfBuiltin, pTerm', parseFile, parseQQ, recordGet, render)
import RIO hiding (Reader, Vector, ask, drop, link, local, replicate, runReader, to, toList)
import System.IO.Unsafe (unsafePerformIO)

nested ∷ Int → TermT → TermT
nested locs = \case
  Block{} → undefined
  Lam arg bod → Lam arg $ recLambda bod
  Op a op b → Op (rec a) op (rec b)
  App f' a' → App (rec f') (rec a')
  old@NatLit{} → old
  old@TagLit{} → old
  FieldsLit flit →
    let with f = case flit of
          Left row → Left $ Lambda $ f (locs + 1) $ unLambda row
          Right record → Right $ f locs record
     in FieldsLit $ with \locs' (Fields knownFields rest) →
          Fields (bimap (nested locs') (nested locs') <$> knownFields) $ nested locs' <$> rest
  Sorry n x → Sorry n $ rec x
  Var i →
    Var
      $ if i >= locs
        then i + 1
        else i
  Quantification q n k in_ → Quantification q n (rec k) (recLambda in_)
  Pi in_ out_ → Pi (rec in_) (either (Left . fmap recLambda) (Right . rec) out_)
  old@Builtin{} → old
  BuiltinsVar → BuiltinsVar
  ExVar n globalI t → ExVar n globalI $ rec <$> t
  UniVar n globalI t → UniVar n globalI $ rec t
 where
  rec = nested locs
  recLambda = Lambda . nested (locs + 1) . unLambda

-- class HasTerm m a where
--   extractTerm ∷ a → m TermT
--   mkFromTerm ∷ Proxy m → TermT → a

-- instance (Applicative m) ⇒ HasTerm m TermT where
--   extractTerm t = pure t
--   mkFromTerm _ = id

-- instance (Applicative m) ⇒ HasTerm m (Maybe TermT, TermT) where
--   extractTerm t = pure $ fst t
--   mkFromTerm _ = (,undefined) . Just

-- Update nesting of normalized value
-- insertBinds ∷ Maybe TermT → RevList (Maybe TermT) → RevList (Maybe TermT)
-- insertBinds x xs = error "wrong, should not be nested when Just" $ (fmap (nested 1) <$> xs) `revSnoc` x

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

-- nestedNormBinds ∷ Int → Vector (Maybe PortableTermT) → NormCtx
-- nestedNormBinds nest v = NormBinds nest $ replicate nest Nothing <> v

-- getNest ∷ NormCtx → Int
-- getNest = \case
--   NormBinds _ x → length x
--   NormRewrite x _ _ → x

-- insertBinds ∷ TermT → Vector (Maybe TermT) → Vector (Maybe TermT)
-- insertBinds x xs = xs |> Just x

-- nestNormCtx ∷ NormCtx → NormCtx
-- nestNormCtx = \case
--   NormBinds globals xs → NormBinds globals (xs |> Nothing)
--   a@NormRewrite{} → a -- TODO: is this correct?

nestNormCtx ∷ NormCtx → NormCtx
nestNormCtx = \case
  NormBinds xs → NormBinds $ (fmap (nested 0) <$> xs) |> Nothing
  NormRewrite a b → NormRewrite (nested 0 a) (nested 0 b)

insertBinds ∷ TermT → Vector (Maybe TermT) → Vector (Maybe TermT)
insertBinds new binds = (fmap (nested 0) <$> binds) |> Just new

applyLambda ∷ Lambda TermT → TermT → TermT
applyLambda bod val = normalize (NormBinds [Just val]) $ unLambda bod

-- TODO: HasTerm
normalize ∷ NormCtx → TermT → TermT
normalize = \ctx term → case ctx of
  NormBinds{} → simplify ctx term
  NormRewrite from to →
    case isEq from term of
      EqYes → to
      _ → simplify (NormRewrite from to) term
 where
  simplify ∷ NormCtx → TermT → TermT
  simplify ctx = \case
    Block (BlockLet _ _ val into)
      | NormBinds binds ← ctx →
          let val' = normalize ctx val
           in normalize
                (NormBinds $ insertBinds val' binds)
                $ unLambda into
      | otherwise → undefined
    Block (BlockRewrite from to) → Block $ (BlockRewrite (normalize ctx from) (normalize ctx to))
    Lam arg bod → Lam arg $ Lambda $ normalize (nestNormCtx ctx) $ unLambda bod
    Op aT op bT →
      let
        aT' = normalize ctx aT
        bT' = normalize ctx bT
       in
        case (aT', bT') of
          (NatLit a, NatLit b) → NatLit $ case op of
            Add → a + b
            Sub → a - b
            Mul → a * b
            Div → a `div` b
          _ → Op aT' op bT'
    App f a →
      let
        f' = normalize ctx f
        a' = normalize ctx a
       in
        case f' of
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
    NatLit x → NatLit x
    TagLit x → TagLit x
    -- -- TODO: for now, no checks that the tail is a valid one.
    -- -- FieldsLit fields [] (Just rest) → _ -- Cool, but not necessary
    FieldsLit fields →
      let
        (ctx', Fields knownFields rest, repack) = case fields of
          Left row → (nestNormCtx ctx, unLambda row, Left . Lambda)
          Right record → (ctx, record, Right)
       in
        FieldsLit
          $ repack
          $ Fields
            (bimap (normalize ctx') (normalize ctx') <$> knownFields)
          $ normalize ctx'
          <$> rest
    Sorry n x → Sorry n $ normalize ctx x
    Var i → case ctx of
      NormBinds binds →
        let after = drop (length binds - i - 1) binds
         in case after of
              (viewl → Just (Just val, _)) → val
              _ → Var $ i - foldl' (\acc x → if isJust x then acc + 1 else acc) 0 after
      NormRewrite{} → Var i
    Quantification q x a b → Quantification q x (normalize ctx a) $ Lambda $ normalize (nestNormCtx ctx) $ unLambda b
    Builtin x → Builtin x
    BuiltinsVar → FieldsLit $ Right $ Fields ((\b → (TagLit $ identOfBuiltin b, Builtin b)) <$> builtinsList) Nothing
    Pi inT outT →
      let
        outT' = case outT of
          Left (n, x) → Left $ (n,) $ Lambda $ normalize (nestNormCtx ctx) $ unLambda x
          Right x → Right $ normalize ctx x
       in
        Pi (normalize ctx inT) outT'
    ExVar n i t → ExVar n i $ normalize ctx <$> t
    UniVar n i t → UniVar n i $ normalize ctx t

--  extractVar var = maybe (pure Nothing) extractTerm $ HM.lookup var binds

normalizeBuiltin ∷ TermT → TermT
normalizeBuiltin = normalize (NormBinds $ Just . Builtin <$> fromList builtinsList)

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
  render $ pTerm' $ normalize (NormBinds []) t
