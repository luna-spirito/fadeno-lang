{- HLINT ignore "Use const" -}
module Context where

import RIO hiding (runReader, Vector)
import Control.Carrier.State.Church (StateC, evalState, modify, runState)
import Parser (OpaqueId, Term (..), Lambda, Quant, Ident, TermF (..), pTerm, regIdent, Module, loadModule', render)
import Prettyprinter.Render.Terminal
import Prettyprinter (Doc, annotate, (<+>), line, group, nest)
import Data.RRBVector (Vector, (|>), viewr, viewl)
import Control.Carrier.Lift (LiftC, sendM, liftWith, runM)
import Control.Effect.State (get, State, state)
import qualified NameGen as N
import qualified RIO.HashMap as HM
import System.OsPath (OsPath)
import Control.Algebra
import Control.Carrier.Error.Church (ErrorC, runError)
import Control.Effect.Error

-- | (Un)Surprisinlgly, Church State outperformed IORef and mopped floor with it.

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

-- TODO: Redesign this to use a proper monadic stack I guess... yeah... wonderful...

data Env = Env
  { envFresh :: !Int
  , envNames :: !N.UsedNames
  , envOpaque :: !(HashMap OpaqueId Term)
  , envLog :: !(Vector StackEntry)
  , envImports :: !Imports
  }

type EnvM = StateC Env IO

data Err = Err !(Doc AnsiStyle) | ErrRollback deriving Show
type AppM = ErrorC Err (LiftC EnvM)

printErr :: Err → Doc AnsiStyle
printErr e = annotate (color Red) "error:" <+> case e of
  ErrRollback → "(uncatched rollback)"
  Err f → f

-- | Run app gracefully
runApp :: AppM a → IO (Vector StackEntry, Either Err a)
runApp = runState (\a b → pure (envLog a, b)) (Env 0 N.emptyUsedNames mempty mempty $ Imports []) . runM . runError (pure . Left) (pure . Right)

-- | Execute app, report errors to std
execAppStd :: AppM a → IO (Maybe a)
execAppStd act = do
  (logs, r) ← runApp act
  case r of
    Left e → do
      render $ pStacks logs
        <> line
        <> printErr e
      pure Nothing
    Right r2 → pure $ Just r2


type ScopesM = StateC Scopes AppM

runScopes :: ScopesM a → AppM a
runScopes = evalState @Scopes (Scopes [] [(Epoch 0, [])] [])

-- funs

loadModule :: OsPath → AppM (Module, Vector OsPath)
loadModule p = do
  names0 ← envNames <$> sendM @EnvM get
  (names, a, b) ← either (throwError . Err . ("parser:" <+>)) pure =<< sendM @EnvM (sendM @IO $ loadModule' names0 p)
  sendM @EnvM $ modify \e → e { envNames = names }
  pure (a, b)

fresh :: AppM Int
fresh = sendM @EnvM $ state @Env \e → (e { envFresh = envFresh e + 1 }, envFresh e)

freshIdent ∷ AppM Ident
freshIdent = regIdent <$> sendM @EnvM (state @Env \e →
  let (newg, n) = N.gen (envNames e)
  in (e { envNames = newg }, n))

registerOpaque :: OpaqueId → Term → AppM ()
registerOpaque i t = sendM @EnvM $ modify @Env \e →
  e { envOpaque = HM.insert i t (envOpaque e) }

getOpaques :: AppM (HashMap OpaqueId Term)
getOpaques = envOpaque <$> sendM @EnvM get

askImports :: AppM Imports
askImports = envImports <$> sendM @EnvM get

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
  sendM @EnvM $ modify @Env \env → env { envLog = envLog env |> StackEntry msg [] }

stackError ∷ ∀ a. ((Term → Doc AnsiStyle) → Doc AnsiStyle) → ScopesM a
stackError ef = do
  stackLog \_ → "<panic!!!11>"
  throwError . Err . ef =<< termLoggerM

stackScope :: ((Term → Doc AnsiStyle) → Doc AnsiStyle) → ScopesM a → ScopesM a
stackScope f act = do
  tl ← termLoggerM
  liftWith @EnvM \hdl ctx → do
    currLog ← state @Env \e → (e { envLog = [] }, envLog e)
    res ← hdl (act <$ ctx)
    modify @Env \e → e { envLog = currLog |> StackEntry (f tl) (envLog e) }
    pure res

getScopeId ∷ Has (State Scopes) sig m ⇒ m Int
getScopeId = (\(Scopes bs _es _rs) → length bs) <$> get @Scopes

getEpoch ∷ Has (State Scopes) sig m ⇒ m Epoch
getEpoch = maybe (error "Missing ex scope") (fst . snd) . (\(Scopes _ es _) → viewr es) <$> get @Scopes

dyn ∷ Has (State Scopes) sig m ⇒ Term → m Dyn
dyn x = (`Dyn` x) <$> getEpoch

-- | Unwraps a term that contains existentials
fetchWith ∷ (Term → ScopesM Term) → Dyn → ScopesM Term
fetchWith f (Dyn objEpoch x) = do
  epoch ← getEpoch
  if epoch == objEpoch
    then pure x
    else f x

pStacks ∷ Vector StackEntry → Doc AnsiStyle
pStacks = viewl >>> \case
  Nothing → mempty
  Just (x, []) → line <> "└ " <> pStack x
  Just (x, xs) → line <> "├ " <> pStack x <> pStacks xs

pStack ∷ StackEntry → Doc AnsiStyle
pStack (StackEntry x xs) = group x <> nest 2 (pStacks xs)
