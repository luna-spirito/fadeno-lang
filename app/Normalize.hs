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
  -- ExVar ex (origValN, origMetaN) →
  --   ExVar
  --     ex
  --     ( if origValN >= fstGlobal -- >, not >=!
  --         then origValN + valBy
  --         else origValN
  --     , origMetaN + metaBy
  --     )
  old@ExVar{} → _
  old@ExVar{} → _
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

{-
-- | Intensional equality.
data EqRes
  = EqYes -- provably eq
  | EqNot -- provably uneq
  | EqUnknown

{- | Checks if two normalized terms are intensionally equivalent.
TODO: η-conversion
-}
isEq ∷ (Has (Lift IO) sig m) ⇒ TermT → TermT → m EqRes
isEq = curry \case
  (Block{}, _) → undefined
  (_, Block{}) → undefined
  (Var a, Var b)
    | a == b → pure EqYes
  (Var _, _) → pure EqUnknown
  (_, Var _) → pure EqUnknown
  (UniVar a1 b1 _, UniVar a2 b2 _)
    | a1 == a2 && b1 == b2 → pure EqYes
  (UniVar{}, _) → pure EqUnknown
  (_, UniVar{}) → pure EqUnknown
  -- TODO: ExVar? I don't know!
  (ExVar{}, _) → error "TODO"
  (_, ExVar{}) → error "TODO"
  (App f1 a1, App f2 a2) → tryEq f1 f2 $ tryEq a1 a2 $ pure EqYes
  (App{}, _) → pure EqUnknown
  (_, App{}) → pure EqUnknown
  (Op a1 op1 b1, Op a2 op2 b2)
    | op1 == op2 → tryEq a1 a2 $ tryEq b1 b2 $ pure EqYes
  (Op{}, _) → pure EqUnknown
  (_, Op{}) → pure EqUnknown
  (Sorry _ a, b) → isEq a b
  (a, Sorry _ b) → isEq a b
  -- Literals
  (Lam _ bod1, Lam _ bod2) → isEq bod1 bod2
  (Lam _ _, _) → pure EqNot
  (NatLit a, NatLit b)
    | a == b → pure EqYes
  (NatLit _, _) → pure EqNot
  (TagLit a, TagLit b)
    | a == b → pure EqYes
  (TagLit _, _) → pure EqNot
  (Quantification q1 _n1 k1 t1, Quantification q2 _n2 k2 t2)
    | q1 == q2 → tryEq k1 k2 $ tryEq t1 t2 $ pure EqYes
  (Quantification{}, _) → pure EqUnknown
  (Builtin a, Builtin b)
    | a == b → pure EqYes
  (Builtin _, _) → pure EqNot
  (_, Builtin _) → pure EqNot
  (BuiltinsVar, BuiltinsVar) → pure EqYes
  (BuiltinsVar, _) → pure EqNot
  (_, BuiltinsVar) → pure EqNot
  -- TODO: Handle mixed?
  (Pi (Just _) inT1 outT1, Pi (Just _) inT2 outT2) →
    isEq inT1 inT2 >>= \case
      EqYes → isEq outT1 outT2
      x → pure x
  (Pi Nothing inT1 outT1, Pi Nothing inT2 outT2) →
    isEq inT1 inT2 >>= \case
      EqYes → isEq outT1 outT2
      x → pure x
  (Pi{}, _) → pure EqNot
  (FieldsLit _ _ _, _) → error "isEq Fields todo"
 where
  -- TODO: FRow???
  tryEq a b cont =
    isEq a b >>= \case
      EqYes → cont
      _ → pure EqUnknown

data NormCtx
  = NormBinds !Int !(Vector (Maybe PortableTermT)) -- Globals, variables.
  | NormRewrite !Int !TermT !TermT -- on normalized. Nestness, from, to.

nestedNormBinds ∷ Int → Vector (Maybe PortableTermT) → NormCtx
nestedNormBinds nest v = NormBinds nest $ replicate nest Nothing <> v

getNest ∷ NormCtx → Int
getNest = \case
  NormBinds _ x → length x
  NormRewrite x _ _ → x

-- insertBinds ∷ TermT → Vector (Maybe TermT) → Vector (Maybe TermT)
-- insertBinds x xs = xs |> Just x

-- nestNormCtx ∷ NormCtx → NormCtx
-- nestNormCtx = \case
--   NormBinds xs → NormBinds $ (fmap (nestedVal 1) <$> xs) |> Nothing
--   NormRewrite a b → NormRewrite (nestedVal 1 a) (nestedVal 1 b)
nestNormCtx ∷ NormCtx → NormCtx
nestNormCtx = \case
  NormBinds globals xs → NormBinds globals (xs |> Nothing)
  a@NormRewrite{} → a -- TODO: is this correct?

-- TODO: HasTerm
-- Normalizes/rewrites a term.
-- `NormBinds globals binds` normalizes a term using `binds`, considering first `globals` `binds` as, well, "globals", and does not erase them.
-- The result term is a valid one under the "globals", and can be normalized again.
-- `NormRewrite nest from term` performs a rewrite, with nesting being `nest`.
normalize ∷ ∀ m sig. (Has (Lift IO) sig m) ⇒ NormCtx → TermT → m TermT
normalize = \ctx term → case ctx of
  NormBinds{} → simplify ctx term
  NormRewrite n from to →
    isEq from term >>= \case
      EqYes → pure to
      _ → simplify (NormRewrite n from to) term
 where
  simplify ∷ NormCtx → TermT → m TermT
  simplify ctx = \case
    Block (BlockLet _ _ val) into
      | NormBinds globals binds ← ctx → do
          val' ← normalize ctx val
          normalize
            (NormBinds globals $ binds |> Just (PortableTerm (getNest ctx) val'))
            into
      | otherwise → undefined
    Block (BlockRewrite from) to → Block <$> (BlockRewrite <$> normalize ctx from) <*> normalize ctx to
    Lam arg bod → Lam arg <$> normalize (nestNormCtx ctx) bod
    Op aT op bT → do
      aT' ← normalize ctx aT
      bT' ← normalize ctx bT
      case (aT', bT') of
        (NatLit a, NatLit b) → pure $ NatLit $ case op of
          Add → a + b
          Sub → a - b
          Mul → a * b
          Div → a `div` b
        _ → pure $ Op aT' op bT'
    App f a → do
      f' ← normalize ctx f
      a' ← normalize ctx a
      case f' of
        Lam _ bod → normalize (NormBinds 0 [Just $ PortableTerm (getNest ctx) a']) bod
        App (Builtin RecordGet) name → do
          let rec = a'
          let search = \case
                FieldsLit FRecord [] (Just rest) → search rest
                FieldsLit FRecord ((name2, val) : xs) rest
                  | name == name2 → val
                  | otherwise → search $ FieldsLit FRecord xs rest
                x → recordGet name x
          pure $ search rec
        _ → pure $ App f' a'
    NatLit x → pure $ NatLit x
    TagLit x → pure $ TagLit x
    -- TODO: for now, no checks that the tail is a valid one.
    -- FieldsLit fields [] (Just rest) → _ -- Cool, but not necessary
    FieldsLit fields origKnown origRest →
      let
        ctx' = case fields of
          FRecord → ctx
          FRow → nestNormCtx ctx
       in
        FieldsLit fields
          <$> (for origKnown \(n, v) → (,) <$> normalize ctx' n <*> normalize ctx' v)
          <*> for origRest (normalize ctx')
    Sorry n x → Sorry n <$> normalize ctx x
    Var i → case ctx of
      NormBinds globals binds →
        let (before, after) = splitAt i binds
         in pure case after of
              (viewl → Just (Just val, _)) → unport val $ getNest ctx
              _ → Var $ i - foldl' (\acc x → if isJust x then acc + 1 else acc) 0 (drop globals before)
      NormRewrite{} → pure $ Var i
    Quantification q x a b → Quantification q x <$> normalize ctx a <*> normalize (nestNormCtx ctx) b
    Builtin x → pure $ Builtin x
    BuiltinsVar → pure $ FieldsLit FRecord ((\b → (TagLit $ identOfBuiltin b, Builtin b)) <$> builtinsList) Nothing
    Pi aM b c → Pi aM <$> normalize ctx b <*> normalize (if isJust aM then nestNormCtx ctx else ctx) c
    old@(ExVar (ExVar' var)) →
      sendIO (readIORef var) >>= \case
        Left t → normalize ctx $ unport t $ getNest ctx
        Right _ → pure old
    old@(UniVar{}) → pure old

--  extractVar var = maybe (pure Nothing) extractTerm $ HM.lookup var binds

normalizeBuiltin ∷ TermT → TermT
normalizeBuiltin = unsafePerformIO . normalize (NormBinds 0 $ Just . PortableTerm 0 . Builtin <$> fromList builtinsList)

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
  render . pTerm' =<< normalize (NormBinds 0 []) t
-}
