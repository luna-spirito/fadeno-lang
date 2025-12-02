{- HLINT ignore "Use const" -}
module Context where

import Control.Algebra
import Control.Carrier.Error.Church (ErrorC, runError)
import Control.Carrier.Fresh.Church (FreshC, runFresh)
import Control.Carrier.Reader (ReaderC, runReader)
import Control.Carrier.State.Church (StateC, evalState, modify)
import Control.Carrier.Writer.Church (WriterC, runWriter)
import Control.Effect.Error
import Control.Effect.Lift (sendIO)
import Control.Effect.State (State, get, put, state)
import Control.Effect.Writer (censor, tell)
import Data.RRBVector (Vector, viewl, viewr)
import NameGen qualified as N
import Parser (Ident, Lambda, Module, OpaqueId, Quant, Term (..), TermF (..), loadModule', pTerm, regIdent, render)
import Prettyprinter (Doc, annotate, group, line, nest, (<+>))
import Prettyprinter.Render.Terminal
import RIO hiding (Vector, runReader)
import RIO.HashMap qualified as HM
import System.OsPath (OsPath)

{- | (Un)Surprisinlgly, Church State outperformed IORef and mopped floor with it.
TODO: We should *probably* get rid of `IO` in `AppM`. It's dead weight for `infer` & `normalize`, although we probably don't
have any _noticeable_ performance hits from it.
-}

-- Fused effects & `Has Ctx sig m` is great, but
-- we have serious performance issues. So this is a dumb monomorphic solution.
-- Is it safe? Obviously, no.

type Binding = (Quant, Maybe Ident, Maybe Term, Term)

newtype Epoch = Epoch Int deriving (Show, Eq)
data Dyn = Dyn !Epoch !Term

data Rewrite = Rewrite !Int !(Lambda (Term, Term)) deriving (Eq, Show) -- (foralls, from, to)

data EEntry
  = EMarker
  | EVar !Int !(Either (Int, Term) Term) -- ExVarId, valty
  | EUniVar !Int
  | ERewrite !Rewrite
  deriving (Eq, Show)
data Scopes = Scopes !(Vector Binding) !(Vector (Epoch, Vector EEntry)) !(Vector (Int, Rewrite)) -- (bindings, metas, index of rewrites from metas)
-- Note: the `rs` vector is "just an index". Sad.

newtype Imports = Imports (Vector (Term, Term)) -- (module, module type)

-- stack

-- | Debug stack
data StackEntry = StackEntry !(Doc AnsiStyle) !(Vector StackEntry)

type AppM = ErrorC (Doc AnsiStyle) (WriterC (Vector StackEntry) (StateC (HashMap OpaqueId Term) (StateC N.UsedNames (FreshC IO))))

-- | Run app gracefully
runApp ∷ AppM a → IO (Vector StackEntry, Either (Doc AnsiStyle) a)
runApp =
  runFresh (\_ → pure) 0
    . evalState N.emptyUsedNames
    . evalState @(HashMap OpaqueId Term) mempty
    . runWriter @(Vector StackEntry) (curry pure)
    . runError @(Doc AnsiStyle) (pure . Left) (pure . Right)

-- | Execute app, report errors to std
execAppStd ∷ AppM a → IO (Maybe a)
execAppStd act = do
  (logs, r) ← runApp act
  case r of
    Left e → do
      render
        $ pStacks logs
        <> line
        <> annotate (color Red) "error: "
        <> e
      pure Nothing
    Right r2 → pure $ Just r2

type ScopesM = StateC Scopes (ReaderC Imports AppM)

runScopes ∷ Imports → ScopesM a → AppM a
runScopes i = runReader i . evalState @Scopes (Scopes [] [(Epoch 0, [])] [])

-- funs

loadModule ∷ OsPath → AppM (Module, Vector OsPath)
loadModule p = do
  names0 ← get
  (names, a, b) ← either (throwError . ("parser:" <+>)) pure =<< sendIO (loadModule' names0 p)
  put names
  pure (a, b)

freshIdent ∷ AppM Ident
freshIdent = regIdent <$> state @N.UsedNames N.gen

registerOpaque ∷ OpaqueId → Term → AppM ()
registerOpaque i t = modify $ HM.insert i t

-- logging

termLoggerM ∷ ScopesM (Term → Doc AnsiStyle)
termLoggerM = (\(Scopes ctx _ _) → pTerm $ (\(_, n, t, _) → (n, t >>= asBuiltin)) <$> ctx) <$> get @Scopes
 where
  asBuiltin = \case
    Term (Builtin x) → Just x
    _ → Nothing

stackLog ∷ ((Term → Doc AnsiStyle) → Doc AnsiStyle) → ScopesM ()
stackLog f = do
  msg ← f <$> termLoggerM
  tell @(Vector StackEntry) [StackEntry msg []]

stackError ∷ ∀ a. ((Term → Doc AnsiStyle) → Doc AnsiStyle) → ScopesM a
stackError ef = do
  stackLog \_ → "<panic!!!11>"
  throwError . ef =<< termLoggerM

stackScope ∷ ((Term → Doc AnsiStyle) → Doc AnsiStyle) → ScopesM a → ScopesM a
stackScope f act = do
  tl ← termLoggerM
  censor (\sublog → [StackEntry (f tl) sublog]) act

getScopeId ∷ (Has (State Scopes) sig m) ⇒ m Int
getScopeId = (\(Scopes bs _es _rs) → length bs) <$> get @Scopes

getEpoch ∷ (Has (State Scopes) sig m) ⇒ m Epoch
getEpoch = maybe (error "Missing ex scope") (fst . snd) . (\(Scopes _ es _) → viewr es) <$> get @Scopes

dyn ∷ (Has (State Scopes) sig m) ⇒ Term → m Dyn
dyn x = (`Dyn` x) <$> getEpoch

-- | Unwraps a term that contains existentials
fetchWith ∷ (Term → ScopesM Term) → Dyn → ScopesM Term
fetchWith f (Dyn objEpoch x) = do
  epoch ← getEpoch
  if epoch == objEpoch
    then pure x
    else f x

pStacks ∷ Vector StackEntry → Doc AnsiStyle
pStacks =
  viewl >>> \case
    Nothing → mempty
    Just (x, []) → line <> "└ " <> pStack x
    Just (x, xs) → line <> "├ " <> pStack x <> pStacks xs

pStack ∷ StackEntry → Doc AnsiStyle
pStack (StackEntry x xs) = group x <> nest 2 (pStacks xs)
