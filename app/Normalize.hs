module Normalize where

import Control.Algebra
import Control.Effect.Lift (Lift, sendIO)
import Data.List (splitAt)
import Language.Haskell.TH.Quote (QuasiQuoter (..))
import Parser (BlockT (..), BuiltinT (..), ExVar' (..), Fields (..), OpT (..), RevList (..), TermT (..), builtinsList, identOfBuiltin, pTerm', parseFile, parseQQ, recordGet, render, revSnoc)
import RIO hiding (Reader, ask, link, local, runReader, toList)
import System.IO.Unsafe (unsafePerformIO)

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
nest ∷ TermT → TermT
nest = rec (0 ∷ Int)
 where
  rec fstGlobal =
    let u x = if x >= fstGlobal then x + 1 else x
     in \case
          Block{} → undefined
          Lam arg bod → Lam arg $ rec (fstGlobal + 1) bod
          Op a op b → Op (rec fstGlobal a) op (rec fstGlobal b)
          App f' a' → App (rec fstGlobal f') (rec fstGlobal a')
          old@NatLit{} → old
          old@TagLit{} → old
          FieldsLit f' a b → FieldsLit f' (bimap (rec fstGlobal) (rec fstGlobal) <$> a) (rec fstGlobal <$> b)
          old@Sorry{} → old
          Var i → Var $ u i
          Quantification q n k in_ → Quantification q n (rec fstGlobal k) (rec fstGlobal in_)
          Pi nameM in_ out_ → Pi nameM (rec fstGlobal in_) (rec fstGlobal out_)
          old@Builtin{} → old
          BuiltinsVar → BuiltinsVar
          ExVar ex k → ExVar ex $ u k
          UniVar a b c → UniVar a (u b) (rec fstGlobal c)

insertBinds ∷ Maybe TermT → RevList (Maybe TermT) → RevList (Maybe TermT)
insertBinds x xs = (fmap nest <$> xs) `revSnoc` x

normalize ∷ ∀ m sig. (Has (Lift IO) sig m) ⇒ RevList (Maybe TermT) → TermT → m TermT
normalize binds = \case
  Block (BlockLet _ _ val) into → do
    val' ← normalize binds val
    normalize
      (insertBinds (Just val') binds)
      into
  Block (BlockRewrite _) into → pure into
  Lam arg bod → Lam arg <$> normalize (insertBinds Nothing binds) bod
  Op aT op bT → do
    aT' ← normalize binds aT
    bT' ← normalize binds bT
    case (aT', bT') of
      (NatLit a, NatLit b) → pure $ NatLit $ case op of
        Add → a + b
        Sub → a - b
        Mul → a * b
        Div → a `div` b
      _ → pure $ Op aT' op bT'
  App f a → do
    f' ← normalize binds f
    a' ← normalize binds a
    case f' of
      Lam _ bod → normalize [Just a'] bod
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
      binds' = case fields of
        FRecord → binds
        FRow → insertBinds Nothing binds
     in
      FieldsLit fields
        <$> (for origKnown \(n, v) → (,) <$> normalize binds' n <*> normalize binds' v)
        <*> for origRest (normalize binds')
  Sorry n x → Sorry n <$> normalize binds x
  Var i →
    let (later, earlier) = splitAt i $ unUnsafeRevList binds
     in pure case earlier of
          [] → Var i
          (Just val : _) → val
          (Nothing : _) → Var $ i - length (catMaybes later)
  Quantification q x a b → Quantification q x <$> normalize binds a <*> normalize (insertBinds Nothing binds) b
  Builtin x → pure $ Builtin x
  BuiltinsVar → pure $ FieldsLit FRecord ((\b → (TagLit $ identOfBuiltin b, Builtin b)) <$> builtinsList) Nothing
  Pi aM b c → Pi aM <$> normalize binds b <*> normalize (if isJust aM then insertBinds Nothing binds else binds) c
  old@(ExVar (ExVar' var) _) →
    sendIO (readIORef var) >>= \case
      Left t → normalize binds t
      Right _ → pure old
  old@(UniVar{}) → pure old

-- where
--  extractVar var = maybe (pure Nothing) extractTerm $ HM.lookup var binds

normalizeBuiltin ∷ TermT → TermT
normalizeBuiltin = unsafePerformIO . normalize (Just . Builtin <$> UnsafeRevList builtinsList)

-- | Parse builtin
parseBQQ ∷ QuasiQuoter
parseBQQ =
  QuasiQuoter
    { quoteExp = \s → ⟦normalizeBuiltin $(quoteExp (parseQQ $ identOfBuiltin <$> UnsafeRevList builtinsList) s)⟧
    , quotePat = error "No pattern support"
    , quoteType = error "No type support"
    , quoteDec = error "No declaration support"
    }

normalizeFile ∷ FilePath → IO ()
normalizeFile x = do
  t ← parseFile x
  render . pTerm' =<< normalize [] t
