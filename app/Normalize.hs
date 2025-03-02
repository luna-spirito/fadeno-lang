module Normalize where

import Control.Algebra
import Control.Effect.Lift (Lift, sendIO)
import Language.Haskell.TH.Quote (QuasiQuoter (..))
import Parser qualified as P
import Prettyprinter (pretty, (<+>))
import RIO hiding (Reader, ask, link, local, runReader, toList)
import RIO.HashMap qualified as HM
import System.IO.Unsafe (unsafePerformIO)

class HasTerm m a where
  extractTerm ∷ a → m (Maybe P.TermT)
  mkFromTerm ∷ Proxy m → P.TermT → a

instance (Applicative m) ⇒ HasTerm m P.TermT where
  extractTerm t = pure $ Just t
  mkFromTerm _ = id

instance (Applicative m) ⇒ HasTerm m (Maybe P.TermT, P.TermT) where
  extractTerm t = pure $ fst t
  mkFromTerm _ = (,undefined) . Just

-- TODO: Something needs to be done to handle ExVar
normalize ∷ ∀ a m sig. (HasTerm m a, Has (Lift IO) sig m) ⇒ HashMap P.Ident a → P.TermT → m P.TermT
normalize binds = \case
  P.Block (P.BlockLet name _ val) into → do
    val' ← normalize binds val
    normalize
      (HM.insert name (mkFromTerm (Proxy @m) val') binds)
      into
  P.Block (P.BlockRewrite _) into → pure into
  P.Lam arg bod → P.Lam arg <$> normalize binds bod
  P.Op aT op bT → do
    aT' ← normalize binds aT
    bT' ← normalize binds bT
    case (aT', bT') of
      (P.NatLit a, P.NatLit b) → pure $ P.NatLit $ case op of
        P.Add → a + b
        _ → error $ show $ "TODO:" <+> pretty a <+> P.pOp op <+> pretty b
      _ → pure $ P.Op aT' op bT'
  P.App (P.App (P.Builtin P.RecordGet) name) rec → do
    name' ← normalize binds name
    let search = \case
          P.FieldsLit P.FRecord [] (Just rest) → search rest
          P.FieldsLit P.FRecord ((name2, val) : xs) rest
            | name' == name2 → val
            | otherwise → search $ P.FieldsLit P.FRecord xs rest
          x → P.recordGet name x
    search <$> normalize binds rec -- TODO: normalize is expensive.
  P.App f a → do
    a' ← normalize binds a
    f' ← normalize binds f
    case f' of
      P.Lam arg bod → normalize (HM.insert arg (mkFromTerm (Proxy @m) a') binds) bod
      _ → pure $ P.App f' a'
  P.NatLit x → pure $ P.NatLit x
  P.TagLit x → pure $ P.TagLit x
  -- TODO: for now, no checks that the tail is a valid one.
  P.FieldsLit fields [] Nothing → pure $ P.FieldsLit fields [] Nothing
  P.FieldsLit _ [] (Just rest) → normalize binds rest
  P.FieldsLit fields ((name, val) : xs) rest → do
    name' ← normalize binds name
    val' ← normalize binds val
    binds' ← case fields of
      P.FRecord → pure binds
      P.FRow → do
        let selfId = P.Ident "self"
        oldSelf ← extractVar selfId
        pure $ HM.insert selfId (mkFromTerm (Proxy @m) $ P.FieldsLit P.FRecord [(name, P.recordGet name' $ P.Var selfId)] oldSelf) binds
    -- TODO: add a new field, `(name, self.name)`?
    xsrest' ←
      normalize
        binds'
        $ P.FieldsLit fields xs rest
    pure $ case xsrest' of
      P.FieldsLit fields2 xs' rest'
        | fields == fields2 → P.FieldsLit fields ((name', val') : xs') rest'
      _ → P.FieldsLit fields [(name', val')] $ Just xsrest'
  P.Sorry n x → P.Sorry n <$> normalize binds x
  P.Var x → fromMaybe (P.Var x) <$> extractVar x
  P.Quantification q x a b → P.Quantification q x <$> normalize binds a <*> normalize (HM.delete x binds) b
  P.Builtin x → pure $ P.Builtin x -- TODO
  P.BuiltinsVar → pure $ P.FieldsLit P.FRecord ((\b → (P.TagLit $ P.identOfBuiltin b, P.Builtin b)) <$> P.builtinsList) Nothing
  P.Pi aM b c → P.Pi aM <$> normalize binds b <*> normalize (maybe id HM.delete aM binds) c
  -- P.Ty → pure P.Ty
  old@(P.ExVar (P.ExVar' var)) →
    sendIO (readIORef var) >>= \case
      Left t → normalize binds t
      Right _ → pure old
  old@(P.UniVar{}) → pure old
 where
  extractVar var = maybe (pure Nothing) extractTerm $ HM.lookup var binds

normalizeBuiltin ∷ P.TermT → P.TermT
normalizeBuiltin = unsafePerformIO . normalize (HM.fromList $ (\b → (P.identOfBuiltin b, P.Builtin b)) <$> P.builtinsList)

-- | Parse builtin
parseBQQ ∷ QuasiQuoter
parseBQQ =
  QuasiQuoter
    { quoteExp = \s → ⟦normalizeBuiltin $(quoteExp P.parseQQ s)⟧
    , quotePat = error "No pattern support"
    , quoteType = error "No type support"
    , quoteDec = error "No declaration support"
    }
