module Normalize where

import Control.Algebra
import Control.Effect.Lift (Lift, sendIO)
import Language.Haskell.TH.Quote (QuasiQuoter (..))
import Parser qualified as P
import Prettyprinter (pretty, (<+>))
import RIO hiding (Reader, ask, link, local, runReader, toList)
import System.IO.Unsafe (unsafePerformIO)

-- class HasTerm m a where
--   extractTerm ∷ a → m P.TermT
--   mkFromTerm ∷ Proxy m → P.TermT → a

-- instance (Applicative m) ⇒ HasTerm m P.TermT where
--   extractTerm t = pure t
--   mkFromTerm _ = id

-- instance (Applicative m) ⇒ HasTerm m (Maybe P.TermT, P.TermT) where
--   extractTerm t = pure $ fst t
--   mkFromTerm _ = (,undefined) . Just

-- Update nesting of normalized value
nest ∷ P.TermT → P.TermT
nest = rec (0 ∷ Int)
 where
  rec fstGlobal =
    let u x = if x >= fstGlobal then x + 1 else x
     in \case
          P.Block{} → undefined
          P.Lam arg bod → P.Lam arg $ rec (fstGlobal + 1) bod
          P.Op a op b → P.Op (rec fstGlobal a) op (rec fstGlobal b)
          P.App f' a' → P.App (rec fstGlobal f') (rec fstGlobal a')
          old@P.NatLit{} → old
          old@P.TagLit{} → old
          P.FieldsLit f' a b → P.FieldsLit f' (bimap (rec fstGlobal) (rec fstGlobal) <$> a) (rec fstGlobal <$> b)
          old@P.Sorry{} → old
          P.Var i → P.Var $ u i
          P.Quantification q n k in_ → P.Quantification q n (rec fstGlobal k) (rec fstGlobal in_)
          P.Pi nameM in_ out_ → P.Pi nameM (rec fstGlobal in_) (rec fstGlobal out_)
          old@P.Builtin{} → old
          P.BuiltinsVar → P.BuiltinsVar
          P.ExVar ex k → P.ExVar ex $ u k
          P.UniVar a b c → P.UniVar a (u b) (rec fstGlobal c)

insertBinds ∷ Maybe P.TermT → [Maybe P.TermT] → [Maybe P.TermT]
insertBinds x xs = x : (fmap nest <$> xs)

normalize ∷ ∀ m sig. (Has (Lift IO) sig m) ⇒ [Maybe P.TermT] → P.TermT → m P.TermT
normalize binds = \case
  P.Block (P.BlockLet _ _ val) into → do
    val' ← normalize binds val
    normalize
      (insertBinds (Just val') binds)
      into
  P.Block (P.BlockRewrite _) into → pure into
  P.Lam arg bod → P.Lam arg <$> normalize (insertBinds Nothing binds) bod
  P.Op aT op bT → do
    aT' ← normalize binds aT
    bT' ← normalize binds bT
    case (aT', bT') of
      (P.NatLit a, P.NatLit b) → pure $ P.NatLit $ case op of
        P.Add → a + b
        _ → error $ show $ "TODO:" <+> pretty a <+> P.pOp op <+> pretty b
      _ → pure $ P.Op aT' op bT'
  P.App f a → do
    f' ← normalize binds f
    a' ← normalize binds a
    case f' of
      P.Lam _ bod → normalize [Just a'] bod
      P.App (P.Builtin P.RecordGet) name → do
        let rec = a'
        let search = \case
              P.FieldsLit P.FRecord [] (Just rest) → search rest
              P.FieldsLit P.FRecord ((name2, val) : xs) rest
                | name == name2 → val
                | otherwise → search $ P.FieldsLit P.FRecord xs rest
              x → P.recordGet name x
        pure $ search rec
      _ → pure $ P.App f' a'
  P.NatLit x → pure $ P.NatLit x
  P.TagLit x → pure $ P.TagLit x
  -- TODO: for now, no checks that the tail is a valid one.
  -- P.FieldsLit fields [] (Just rest) → _ -- Cool, but not necessary
  P.FieldsLit fields origKnown origRest →
    let
      binds' = case fields of
        P.FRecord → binds
        P.FRow → insertBinds Nothing binds
     in
      P.FieldsLit fields
        <$> (for origKnown \(n, v) → (,) <$> normalize binds' n <*> normalize binds' v)
        <*> for origRest (normalize binds')
  P.Sorry n x → P.Sorry n <$> normalize binds x
  P.Var i → pure case drop i binds of
    [] → P.Var i
    (Just val : _) → val
    -- Someone-someone yells that this is wrong. Didn't actually convince me.
    (Nothing : _) → P.Var $ i - length (catMaybes $ take i binds)
  P.Quantification q x a b → P.Quantification q x <$> normalize binds a <*> normalize (insertBinds Nothing binds) b
  P.Builtin x → pure $ P.Builtin x
  P.BuiltinsVar → pure $ P.FieldsLit P.FRecord ((\b → (P.TagLit $ P.identOfBuiltin b, P.Builtin b)) <$> P.builtinsList) Nothing
  P.Pi aM b c → P.Pi aM <$> normalize binds b <*> normalize (if isJust aM then insertBinds Nothing binds else binds) c
  old@(P.ExVar (P.ExVar' var) _) →
    sendIO (readIORef var) >>= \case
      Left t → normalize binds t
      Right _ → pure old
  old@(P.UniVar{}) → pure old

-- where
--  extractVar var = maybe (pure Nothing) extractTerm $ HM.lookup var binds

normalizeBuiltin ∷ P.TermT → P.TermT
normalizeBuiltin = unsafePerformIO . normalize (Just . P.Builtin <$> P.builtinsList)

-- | Parse builtin
parseBQQ ∷ QuasiQuoter
parseBQQ =
  QuasiQuoter
    { quoteExp = \s → ⟦normalizeBuiltin $(quoteExp (P.parseQQ $ P.identOfBuiltin <$> P.builtinsList) s)⟧
    , quotePat = error "No pattern support"
    , quoteType = error "No type support"
    , quoteDec = error "No declaration support"
    }

normalizeFile ∷ FilePath → IO ()
normalizeFile x = do
  t ← P.parseFile x
  P.render . P.pTerm' =<< normalize [] t
