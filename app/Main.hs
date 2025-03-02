{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE ViewPatterns #-}

module Main where

import Control.Algebra
import Control.Carrier.Accum.Church (evalAccum)
import Control.Carrier.Empty.Church (runEmpty)
import Control.Carrier.Error.Church (ErrorC, runError)
import Control.Carrier.Fresh.Church (FreshC, evalFresh)
import Control.Carrier.Lift (LiftC, runM)
import Control.Carrier.Reader (ReaderC, runReader)
import Control.Carrier.State.Church
import Control.Carrier.Writer.Church (WriterC, execWriter, runWriter)
import Control.Effect.Accum (add, look)
import Control.Effect.Empty qualified as E
import Control.Effect.Error (Error, Throw, throwError)
import Control.Effect.Fresh (Fresh, fresh)
import Control.Effect.Lift (Lift, sendIO, sendM)
import Control.Effect.Reader (Reader, ask, local)
import Control.Effect.Writer (Writer, censor, listen, tell)
import Data.Bits (unsafeShiftL, unsafeShiftR, (.&.), (.|.))
import Data.ByteString.Builder (toLazyByteString)
import Data.ByteString.Char8 qualified as BS
import Data.IntMap.Strict qualified as IM
import Data.Kind (Type)
import Data.List (intercalate, uncons)
import Data.Serialize (PutM, execPut, putBuilder, putWord32be, putWord64be, putWord8, runPutMBuilder)
import GHC.Exts (IsList (..))
import Parser qualified as P
import Prettyprinter (Doc, annotate, indent, line, nest, pretty, (<+>))
import Prettyprinter.Render.Terminal (AnsiStyle, Color (..), color)
import RIO hiding (Reader, ask, link, local, runReader, toList)
import RIO.HashMap qualified as HM
import RIO.Partial qualified as P
import RIO.Seq (Seq (..))
import RIO.Seq qualified as S
import RIO.Vector qualified as V
import System.IO (print)
import Type.Reflection ((:~:) (..))

{-
Whenever a node interacts with a negative package, DO NOT UNWRAP.
Instead, create a new, specialized package.

Also, maybe YES sub-packages?, but NO deep substitutions. This messes things up.
What could help is: BI-DIRECTIONALLY phase primary ports through custom node's auxiliary?
This could help even in regular code I guess.
\x
  y = [3, 4, x]
  z = (9, y)
  w = (10, y)
  in (z, w)
... will automatically inline `y`.

So, let's first separate tags and ports?

\y ->
  // x = +> (y, y)
  x = (y, y)
  in MkPair x x

builtins/rec \rec ->
  \y -> if y == 0
    then y*rec (y-1)
    else 0

EDIT: instead of "phasing" primary ports, just fix the entry point and "suck in" all the other nodes.
EDIT: "phasing/sucking in/out" is not that bad since it increases optimality, but it as well reduces the compilation
capabilities by reducing the amount of available information.
"Phasing in" is clearly not as bad as "phasing out", but I'm not sure it's worth the effort and it still can yield worse performance
in some edge cases (ex. partial erasure), although usually it's better.

28.12.24: Phasing in/out, while could be a good thing for optimality, is not always this way.
We'd better stick to the approach of "trusting the programmer", at least for now.
Whatever programmer says to be the node, will be the node, with no "extra"s or "exclusion"s.
Also, we package local variables as a transparent optimization, but we don't guarantee doing this or doing this the best way, but
we do guarantee that we do it only when it preserves optimality.

28.12.24: Solution:
No phasings. Instead, each time a specialisation occurs (i. e. you interact with negative package), DO NOT UNWRAP it.
-}

-- TODO: Currently identifiers with `/` are reserved.
-- Correct type-checking also depends on this. This is absolutely horrible.
-- TODO: just calm down and use freaking substitutions.
-- You can't guarantee correctness of the mess you've written if you
-- continue to do things this way.
-- TODO: meaningful names for compiler-generated Vars, UniVars, ExVars
-- TODO: Type of existential is not checked when instantiating.

{-
13.02.25
I'm currently working on implenting Type universes.
Currently we have <term (3)> : <type (U32)> : Type+ 0 : Type+ 1 : ... : Type+ Aleph

Type+ Aleph doesn't have a type. And, therefore, it can only be inferred, but user can't include it in the code.
EDIT: Since type-checking is undecidable, type-checking type annotations is a horrendously stupid idea.
Aleph will be available at the level of type annotations only.
-}

newtype RevList a = UnsafeRevList [a] deriving (Functor, Show)

instance Semigroup (RevList a) where
  UnsafeRevList a <> UnsafeRevList b = UnsafeRevList $ b <> a

instance Monoid (RevList a) where
  mempty = []

revSnoc ∷ RevList a → a → RevList a
revSnoc (UnsafeRevList ls) x = UnsafeRevList $ x : ls

revUnsnoc ∷ RevList a → Maybe (RevList a, a)
revUnsnoc (UnsafeRevList x) = (\(v, l) → (UnsafeRevList l, v)) <$> uncons x

instance IsList (RevList a) where
  type Item (RevList a) = a
  fromList ls = UnsafeRevList $ reverse ls
  toList (UnsafeRevList ls) = reverse ls

-- censor + listen
intercept ∷ ∀ w m sig a. (Has (Writer w) sig m, Monoid w) ⇒ m a → m (w, a)
intercept = censor @w (const mempty) . listen @w

-- | Debug stack
data StackLog m a where
  StackLog ∷ Doc AnsiStyle → StackLog m ()
  StackScope ∷ Doc AnsiStyle → m a → StackLog m a

-- | Accumulates the stack over the runtime of the program.
newtype StackAccC m a = StackAccC {unStackAccC ∷ WriterC (RevList StackEntry) m a}
  deriving (Functor, Applicative, Monad)

data StackEntry = StackEntry !(Doc AnsiStyle) ![StackEntry]

instance (Algebra sig m) ⇒ Algebra (StackLog :+: sig) (StackAccC m) where
  alg hdl sig ctx = StackAccC $ case sig of
    L (StackLog x) → do
      tell @(RevList StackEntry) [StackEntry x []]
      pure ctx
    L (StackScope name act) → do
      censor (\entries → [StackEntry name $ toList @(RevList _) entries])
        $ unStackAccC
        $ hdl (ctx $> act)
    R other → alg (unStackAccC . hdl) (R other) ctx

stackLog ∷ (Has StackLog sig m) ⇒ Doc AnsiStyle → m ()
stackLog = send . StackLog

stackScope ∷ (Has StackLog sig m) ⇒ Doc AnsiStyle → m a → m a
stackScope name act = send $ StackScope name act

-- Monomorphised to Doc AnsiStyle.
stackError ∷ ∀ sig m a. (Has (StackLog :+: Throw (Doc AnsiStyle)) sig m) ⇒ Doc AnsiStyle → m a
stackError e = do
  stackLog "<panic!!!11>"
  throwError e

-- TODO: Fix the newlines
pStacks ∷ [StackEntry] → Doc AnsiStyle
pStacks = \case
  [] → mempty
  [x] → line <> "└ " <> pStack x
  (x : xs) → line <> "├ " <> pStack x <> pStacks xs

pStack ∷ StackEntry → Doc AnsiStyle
pStack = \(StackEntry x xs) → x <> nest 2 (pStacks xs) where

runStackAccC ∷ (Applicative m) ⇒ StackAccC m a → m ([StackEntry], a)
runStackAccC = runWriter (\w a → pure (toList @(RevList _) w, a)) . unStackAccC

newtype StackPrintC m a = StackPrintC {unStackPrintC ∷ ReaderC Int m a}
  deriving (Functor, Applicative, Monad)

instance (Has (Lift IO) sig m) ⇒ Algebra (StackLog :+: sig) (StackPrintC m) where
  alg hdl sig ctx = StackPrintC case sig of
    L (StackLog msg) → do
      sendMsg msg
      pure ctx
    L (StackScope msg act) → do
      sendMsg msg
      res ← local @Int (+ 1) $ unStackPrintC $ hdl (ctx $> act)
      sendMsg "--"
      pure res
    R other → alg (unStackPrintC . hdl) (R other) ctx
   where
    sendMsg msg = do
      level ← ask
      sendIO $ P.render $ indent (level * 2) $ "├ " <> msg

runStackPrintC ∷ (Has (Lift IO) sig m) ⇒ StackPrintC m a → m a
runStackPrintC = runReader 0 . unStackPrintC

-- Check

-- | Context stores values and the type of introduced bindings.
type CtxT = HashMap P.Ident (Maybe P.TermT, P.TermT) -- Actually stores just Idents, but VarT for easier conversion.

data SEntry = SScope | SExVar

-- | For meta-variables
type Solve = State (IntMap (RevList P.ExVar')) :+: Fresh :+: Error (Doc AnsiStyle) :+: StackLog :+: Lift IO

freshIdent ∷ (Has Solve sig m) ⇒ m P.Ident
freshIdent = P.UIdent <$> fresh

pushExVar ∷ (Has (Writer (RevList P.ExVar') :+: Reader Int :+: Solve) sig m) ⇒ Maybe P.TermT → m P.TermT
pushExVar t = do
  scope ← ask
  name ← freshIdent
  metaVar' ← fmap P.ExVar' $ sendIO $ newIORef $ Right (name, (scope, t))
  tell @(RevList _) [metaVar']
  pure $ P.ExVar metaVar'

pushUniVar ∷ (Has (Reader Int :+: Solve) sig m) ⇒ P.TermT → m P.TermT
pushUniVar ty = do
  -- Pushed ephemerally.
  scope ← ask
  ident ← freshIdent
  pure $ P.UniVar ident scope ty

-- I hate this.
revInsertBefore ∷ ∀ a. RevList a → (a → Bool) → RevList a → RevList a
revInsertBefore ins f = go
 where
  go = \case
    UnsafeRevList [] → []
    UnsafeRevList (x : xs)
      | f x → [x] <> ins <> (UnsafeRevList xs)
      | otherwise →
          let (UnsafeRevList xs') = go $ UnsafeRevList xs
           in UnsafeRevList $ x : xs'

-- Probably access to Solve should be restricted in ExVarPushC...
type ExVarPushC m = ReaderC Int (WriterC (RevList P.ExVar') m)

beforeEx ∷ (Has Solve sig m) ⇒ Int → P.ExVar' → (ExVarPushC m (m a)) → m a
beforeEx scope ex act = do
  (inserted, resM) ← runWriter (curry pure) $ runReader scope act
  modify $ IM.adjust (revInsertBefore inserted (== ex)) scope
  resM

scoped' ∷ (Has Solve sig m) ⇒ ((P.TermT → P.TermT) → a → a) → ExVarPushC m (m a) → m a
scoped' tmap act = do
  scope ← IM.size @(RevList P.ExVar') <$> get
  (origExs, tyM) ← runWriter (curry pure) $ runReader scope act
  modify $ IM.insert scope origExs
  ty ← tyM
  UnsafeRevList exs ← state @(IntMap (RevList P.ExVar')) \scopes →
    (IM.deleteMax scopes, snd $ fromMaybe (error "Internal error: Scope disappeared") $ IM.lookupMax scopes)
  foldM
    ( \ty' (P.ExVar' x) →
        sendIO (readIORef x) >>= \case
          Left t → stackError $ "Internal error: Resolved existential wasn't marked as such:" <+> P.pTerm 0 t
          Right (_, (_, xTyM)) → do
            variable ← fresh
            let variable' = P.Ident $ BS.pack $ "/" <> show variable
            sendIO $ writeIORef x $ Left $ P.Var variable'
            -- TODO: extract name for new variable from the existential.
            let ofT t = P.Quantification P.Forall variable' t `tmap` ty'
            case xTyM of
              Just xTy → pure $ ofT xTy
              Nothing → do
                n ← freshIdent
                pure $ P.Quantification P.Forall n (P.Builtin P.U32) `tmap` ofT (P.typOf $ P.Var n)
    )
    ty
    exs

{-
pushExVarInto :: (Has Solve sig m) => Int -> Maybe P.TermT -> m P.ExVar'
pushExVarInto scope t = do
  name <- freshIdent
  metaVar' <- fmap P.ExVar' $ sendIO $ newIORef $ Right $ (name, (scope, t))
  insMeta scope metaVar'
  pure metaVar'

pushExVar :: (Has Solve sig m) => Maybe P.TermT -> m P.TermT
pushExVar t = do
  scope <- (\x -> x - 1) . IM.size <$> get @(IntMap [P.ExVar'])
  pushExVarInto scope t

scoped :: (Has Solve sig m) => m P.TermT -> m P.TermT
scoped = scoped' id
-- scoped act = do

insMeta :: (Has Solve sig m) => Int -> P.ExVar' -> m ()
insMeta scope var = do
  modify @(IntMap [P.ExVar']) \scopes ->
    IM.adjust (var :) scope scopes

-}
-- Assumes that all existentias are resolved if they are ever used.
scoped_ ∷ (Has Solve sig m) ⇒ ExVarPushC m (m a) → m a
scoped_ act = do
  -- Bad copy-pasta
  scope ← IM.size @(RevList P.ExVar') <$> get
  (origExs, tyM) ← runWriter (curry pure) $ runReader scope act
  modify $ IM.insert scope origExs
  ty ← tyM
  modify $ IM.deleteMax @(RevList P.ExVar')
  pure ty

scoped ∷ (Has Solve sig m) ⇒ ExVarPushC m (m P.TermT) → m P.TermT
scoped = scoped' id

markSolved ∷ (Has Solve sig m) ⇒ Int → P.ExVar' → m ()
markSolved scope var = do
  modify @(IntMap (RevList P.ExVar')) \scopes →
    IM.adjust (\(UnsafeRevList l) → UnsafeRevList $ filter (/= var) l) scope scopes

-- Writes & checks
writeMeta ∷ (Has Solve sig m) ⇒ (Int, Maybe P.TermT) → P.ExVar' → P.TermT → m ()
writeMeta (scope, tyM) (P.ExVar' var) val = do
  for_ tyM $ infer [] val . Check
  -- stackLog $ "?" <> P.pTerm 0 (P.ExVar $ P.ExVar' var) <+> "=" <+> P.pTerm 0 val
  sendIO $ writeIORef var $ Left val
  markSolved scope (P.ExVar' var)

-- TODO: So, return the proper ordering, but just use
instMeta ∷ ∀ sig m. (Has Solve sig m) ⇒ (Int, Maybe P.TermT) → P.ExVar' → P.TermT → m ()
instMeta = (\f a b c → stackScope "instMeta" $ f a b c) \(scope1, t1) origVar1 →
  let instMeta' ∷ P.TermT → m P.TermT
      instMeta' = \case
        P.Sorry _ x → instMeta' x
        P.ExVar (P.ExVar' var2) →
          sendIO (readIORef var2) >>= \case
            Left t → instMeta' t
            Right (_, (scope2, t2)) → do
              -- Either var1 or origVar2 is introduced earlier. We need to identify, which one.
              var2Earlier ←
                if
                  | scope2 < scope1 → pure True
                  | scope2 > scope1 → pure False
                  | otherwise → do
                      -- Well, that's bad, like really bad.
                      let go = \case
                            (x : xs)
                              | x == origVar1 → True -- In RevList, the later one is found first.
                              | x == P.ExVar' var2 → False
                              | otherwise → go xs
                            _ → error "Imposible"
                      UnsafeRevList exs ← P.fromJust . IM.lookup scope1 <$> get
                      pure $ go exs
              if var2Earlier
                then pure $ P.ExVar $ P.ExVar' var2
                else beforeEx scope1 origVar1 do
                  var1R ← pushExVar t2
                  pure do
                    writeMeta (scope2, t2) (P.ExVar' var2) var1R
                    pure var1R
        uni@(P.UniVar _ scope2 _)
          | scope2 <= scope1 → pure uni
        P.App f a → P.App <$> instMeta' f <*> instMeta' a
        P.FieldsLit P.FRow known rest →
          P.FieldsLit P.FRow
            <$> for known (\(a, b) → (a,) <$> instMeta' b)
            <*> for rest instMeta'
        P.Var x → pure $ P.Var x -- TODO: I hope this is correct, but needs to be rechecked.
        P.Builtin x → pure $ P.Builtin x
        P.NatLit x → pure $ P.NatLit x
        P.Pi inNameM inT outT → P.Pi inNameM <$> instMeta' inT <*> instMeta' outT
        P.Op a op b → do
          a' ← instMeta' a
          b' ← instMeta' b
          pure $ P.Op a' op b'
        x → stackError $ "instMeta (of" <+> pretty scope1 <> ")" <+> P.pTerm 0 x
   in \val →
        let r = writeMeta (scope1, t1) origVar1 =<< instMeta' val
         in case val of
              P.ExVar (P.ExVar' var2) →
                if origVar1 == P.ExVar' var2
                  then pure ()
                  else
                    sendIO (readIORef var2) >>= \case
                      Left val' → instMeta (scope1, t1) origVar1 val'
                      _ → r
              _ → r

class HasTerm m a where
  extractTerm ∷ a → m (Maybe P.TermT)
  mkFromTerm ∷ Proxy m → P.TermT → a

data LazyTermT m = LazyTerm !(IORef (m P.TermT)) | LazyPure !P.TermT

instance (Has Solve sig m) ⇒ HasTerm m (LazyTermT m) where
  extractTerm (LazyTerm var) = do
    val ← join $ sendIO $ readIORef var
    sendIO $ writeIORef var $ pure val
    pure $ Just val
  extractTerm (LazyPure x) = pure $ Just x
  mkFromTerm _ = LazyPure

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
  P.BuiltinsVar → pure $ P.FieldsLit P.FRecord (fmap fst <$> P.builtinsVar) Nothing
  P.Pi aM b c → P.Pi aM <$> normalize binds b <*> normalize (maybe id HM.delete aM binds) c
  -- P.Ty → pure P.Ty
  old@(P.ExVar (P.ExVar' var)) →
    sendIO (readIORef var) >>= \case
      Left t → normalize binds t
      Right _ → pure old
  old@(P.UniVar{}) → pure old
 where
  extractVar var = maybe (pure Nothing) extractTerm $ HM.lookup var binds

withMono ∷ (Has Solve sig m) ⇒ ((P.TermT → P.TermT) → a → a) → P.TermT → (P.ExVar' → (Int, Maybe P.TermT) → m a) → (P.TermT → m a) → m a
withMono tmap = \a onMeta onOther → withMono' onMeta onOther a
 where
  withMono' onMeta onOther = \case
    P.Sorry _ v → withMono' onMeta onOther v
    P.ExVar (P.ExVar' var) →
      sendIO (readIORef var) >>= \case
        Left v → withMono' onMeta onOther v
        Right (_, v) → onMeta (P.ExVar' var) v
    P.Quantification P.Forall name kind v → scoped' tmap do
      ty ← pushExVar $ Just kind
      pure $ withMono' onMeta onOther =<< normalize (HM.singleton name ty) v
    P.Quantification P.Exists name kind v → scoped' tmap do
      ty ← pushUniVar kind
      pure $ withMono' onMeta onOther =<< normalize (HM.singleton name ty) v
    r → onOther r

-- | Intensional equality.
data EqRes
  = EqYes -- provably eq
  | EqNot -- provably uneq
  | EqUnknown

data LookupRes
  = LookupFound !(P.TermT) !([(P.TermT, P.TermT)], Maybe P.TermT)
  | LookupMissing
  | LookupUnknown
  deriving (Show)

tmapLookupRes ∷ (P.TermT → P.TermT) → LookupRes → LookupRes
tmapLookupRes f = \case
  LookupFound a b → LookupFound (f a) b
  x → x

-- Lookups in FRow. **FRow**.
-- The type is too restrictive about requiring a continuation.
withLookupField ∷ (Has Solve sig m) ⇒ (LookupRes → m a) → ((P.TermT → P.TermT) → a → a) → Bool → P.TermT → ([(P.TermT, P.TermT)], Maybe P.TermT) → m a
withLookupField cont f refine needle = rec []
 where
  notARow x = stackError $ "Not a row:" <+> P.pTerm 0 x
  rec prev = \case
    ([], Nothing) → cont LookupMissing
    ([], Just next) → withMono
      f
      next
      ( \var →
          if refine
            then \case
              (mScope, Just (P.App (P.Builtin P.Row) mT)) →
                beforeEx mScope var do
                  rest' ← pushExVar (Just $ P.rowOf mT)
                  val' ← pushExVar (Just mT)
                  writeMeta (mScope, Just $ P.rowOf mT) var $ P.FieldsLit P.FRow [(needle, val')] $ Just rest'
                  pure $ cont $ LookupFound val' (toList prev, Just rest')
              _ → notARow $ P.ExVar var
            else const $ cont LookupMissing
      )
      \case
        P.FieldsLit P.FRow vals rest → rec prev (vals, rest)
        x → stackError $ "lookupField todo " <> P.pTerm 0 x
    ((name, val) : xs, rest) →
      isEq needle name >>= \case
        EqYes → cont $ LookupFound val (toList prev <> xs, rest)
        EqUnknown → cont LookupUnknown
        EqNot → rec (prev `revSnoc` (name, val)) (xs, rest)

{- | Checks if two normalized terms are intensionally equivalent.
TODO: η-conversion
-}
isEq ∷ (Has Solve sig m) ⇒ P.TermT → P.TermT → m EqRes
isEq = curry \case
  (P.Block{}, _) → undefined
  (P.Var _, _) → undefined
  (_, P.Block{}) → undefined
  (_, P.Var _) → undefined
  (P.UniVar a _ _, P.UniVar b _ _)
    | a == b → pure EqYes
  (P.UniVar{}, _) → pure EqUnknown
  (_, P.UniVar{}) → pure EqUnknown
  -- TODO: ExVar? I don't know!
  (P.ExVar{}, _) → stackError "isEq ExVar"
  (_, P.ExVar{}) → stackError "isEq ExVar"
  (P.App f1 a1, P.App f2 a2) → tryEq f1 f2 $ tryEq a1 a2 $ pure EqYes
  (P.App{}, _) → pure EqUnknown
  (_, P.App{}) → pure EqUnknown
  (P.Op a1 op1 b1, P.Op a2 op2 b2)
    | op1 == op2 → tryEq a1 a2 $ tryEq b1 b2 $ pure EqYes
  (P.Op{}, _) → pure EqUnknown
  (_, P.Op{}) → pure EqUnknown
  (P.Sorry _ a, b) → isEq a b
  (a, P.Sorry _ b) → isEq a b
  -- (P.BuiltinsVar, b) → isEq builtinsVa
  -- Literals
  (P.Lam arg1 bod1, P.Lam arg2 bod2) → scoped_ do
    arg ← pushUniVar undefined -- "Kind" actually doesn't matter.
    pure do
      bod1' ← normalize (HM.singleton arg1 arg) bod1
      bod2' ← normalize (HM.singleton arg2 arg) bod2
      isEq bod1' bod2'
  (P.Lam _ _, _) → pure EqNot
  (P.NatLit a, P.NatLit b)
    | a == b → pure EqYes
  (P.NatLit _, _) → pure EqNot
  (P.TagLit a, P.TagLit b)
    | a == b → pure EqYes
  (P.TagLit _, _) → pure EqNot
  -- (P.FieldsLit P.FRecord vals1 rest1M, P.FieldsLit P.FRecord vals2 rest2M) →
  --   case (vals1, rest1M) of
  --     ([], Nothing) → case (vals2, rest2M) of
  --       ([], Nothing) → pure EqYes
  --       _ → pure EqNot
  --     ([], Just rest1) → isEq rest1 (P.FieldsLit P.FRecord vals2 rest2M)
  --     ((name1, val1):xs, rest1) →
  --       lookupField False name1 (vals2, rest2M) >>= \case
  --         LookupFound val2 (vals2', rest2') → isEq val1 val2 >>= \case
  --           EqYes → isEq (P.FieldsLit P.FRecord xs rest1) (P.FieldsLit P.FRecord vals2' rest2')
  --           EqNot → pure EqNot
  --           EqUnknown → pure EqUnknown
  --         LookupMissing → pure EqNot
  --         LookupUnknown → pure EqUnknown
  -- (P.FieldsLit P.FRecord _ _, _) → pure EqNot
  (P.Quantification q1 n1 k1 t1, P.Quantification q2 n2 k2 t2)
    | q1 == q2 →
        isEq k1 k2 >>= \case
          EqYes → scoped_ do
            arg ← pushUniVar undefined
            pure do
              t1' ← normalize (HM.singleton n1 arg) t1
              t2' ← normalize (HM.singleton n2 arg) t2
              isEq t1' t2'
          x → pure x
  (P.Quantification{}, _) → pure EqNot
  (P.Builtin a, P.Builtin b)
    | a == b → pure EqYes
  (P.Builtin _, _) → pure EqNot
  (_, P.Builtin _) → pure EqNot
  (P.BuiltinsVar, P.BuiltinsVar) → pure EqYes
  (P.BuiltinsVar, _) → pure EqNot
  (_, P.BuiltinsVar) → pure EqNot
  -- (P.U32, P.U32) → pure EqYes
  -- (P.U32, _) → pure EqNot
  -- (P.Tag, P.Tag) → pure EqYes
  -- (P.Tag, _) → pure EqNot
  -- (P.Row a, P.Row b) → isEq a b
  -- (P.Row _, _) → pure EqNot
  -- TODO: override self as soon as you start type-checking row!
  -- (P.Record x, P.Record y) → isEq x y
  -- (P.Record _, _) → pure EqNot
  (P.Pi inNameM1 inT1 outT1, P.Pi inNameM2 inT2 outT2) →
    isEq inT1 inT2 >>= \case
      EqYes → scoped_ do
        arg ← pushUniVar undefined
        pure do
          outT1' ← maybe pure (\name → normalize $ HM.singleton name arg) inNameM1 outT1
          outT2' ← maybe pure (\name → normalize $ HM.singleton name arg) inNameM2 outT2
          isEq outT1' outT2'
      x → pure x
  (P.Pi{}, _) → pure EqNot
  -- (P.Ty, P.Ty) → pure EqYes
  -- (P.Ty, _) → pure EqNot
  (P.FieldsLit _ _ _, _) → stackError "isEq Fields todo"
 where
  -- (P.Access _ _, _) -> stackError "isEq Access todo" -- Equate all fields that are Unknown eq to tag.

  -- TODO: FRow???
  tryEq a b cont =
    isEq a b >>= \case
      EqYes → cont
      _ → pure EqUnknown

-- TODO: implement rewrite as a normalize subroutine.
-- Rewrites are performed on normalized terms.
-- This makes sense only since current stupid implementation rewrites
-- only the normalized bindings in scope.
-- TODO: rewrite as a form of normalize.
-- rewrite :: forall sig m. (Has Solve sig m) => (P.TermT, P.TermT) -> P.TermT -> m P.TermT
-- rewrite (what, with) = rewrite'
--   where
--     rewrite' :: P.TermT → m P.TermT
--     rewrite' curr = do
--       matches <- isEq what curr
--       case matches of
--         EqYes -> pure with
--         _ -> rec curr
--     -- TODO: This just recurses 1 level into the structure.
--     -- Probably could be deduplicated with instMeta.
--     rec :: P.TermT → m P.TermT
--     rec = \case
--       P.Block {} -> undefined
--       P.Lam argName bod -> scoped_ do
--         arg ← pushUniVar' undefined
--         pure do
--           bod' ← normalize (HM.singleton argName $ P.Var arg) bod
--           bodR ← rewrite' bod'
--           normalize (HM.singleton arg (P.Var $ P.SourceVar argName)) bodR
--       P.Op a op b → P.Op <$> rewrite' a <*> pure op <*> rewrite' b
--       P.App f a → P.App <$> rewrite' f <*> rewrite' a
--       x@(P.NatLit _) → pure x
--       x@(P.TagLit _) → pure x
--       P.FieldsLit f t v → --P.FildsLit f <$> _ <*> _

data InferMode a where
  Infer ∷ InferMode P.TermT
  Check ∷ P.TermT → InferMode ()

infer ∷ ∀ sig m a. (Has Solve sig m) ⇒ CtxT → P.TermT → InferMode a → m a
infer ctx = (\t mode → stackScope (P.pTerm 0 t) $ infer' t mode)
 where
  -- Here, we will convert Checks to Infers.
  -- However, converting Infer to a Check when checking a term is hereby declared a deadly sin.
  infer' = curry \case
    (term, Check (P.Quantification P.Forall xName xTy yT)) → scoped_ do
      x' ← pushUniVar xTy
      pure do
        yT' ← normalize (HM.singleton xName x') yT
        infer ctx term $ Check $ yT'
    -- TODO: breaks.
    -- (term, Check ((P.Quantification P.Exists xName P.Ty yT))) → scoped_ do -- TODO: not just for Ty!
    --   x' ← pushExVar
    --   yT' ← normalize (HM.singleton xName x') yT
    --   infer ctx term $ Check $ yT'
    (P.Block (P.BlockLet name tyM val) into, mode) → do
      ty ← stackScope ("let" <+> P.pIdent name) case tyM of
        Nothing → infer ctx val Infer
        Just ty → do
          -- TODO: check ty' to be a type?
          -- EDIT: typechecking is undecidable... so... uh... no?
          -- void $ infer ctx ty Infer
          ty' ← normalize ctx ty
          infer ctx val $ Check ty'
          pure ty'
      val' ← normalize ctx val
      let withBs' act = case into of
            P.Block{} → stackScope "in" $ act into
            _ → act into
      withBs' \bs' →
        infer
          (HM.insert name (Just val', ty) ctx)
          bs'
          mode
    -- (P.Block (P.BlockRewrite with) into, mode) → _
    (P.Lam arg bod, Infer) →
      scoped do
        u ← pushExVar $ Just $ P.Builtin P.U32
        inT ← pushExVar $ Just $ P.typOf u
        pure do
          outT ← infer (HM.insert arg (Nothing, inT) ctx) bod Infer
          pure $ P.Pi Nothing inT outT
    (P.Lam arg bod, Check (P.Pi inNameM inT outT)) → do
      inT' ← normalize (HM.mapMaybe fst ctx) inT
      let inferBod val outT' = infer (HM.insert arg (val, inT') ctx) bod $ Check outT'
      case inNameM of
        Nothing → inferBod Nothing outT
        Just inName → scoped_ do
          arg' ← pushUniVar inT'
          pure do
            outT' ← normalize (HM.singleton inName arg') outT
            inferBod (Just arg') outT'
    (P.Op a _op b, Infer) → do
      -- Deadly sin. Should be fixed.
      infer ctx a $ Check $ P.Builtin P.U32
      infer ctx b $ Check $ P.Builtin P.U32
      pure $ P.Builtin P.U32
    -- Override for second-class RecordGet
    (P.App (P.App (P.Builtin P.RecordGet) tag) record, Infer) → do
      recordTy ← infer ctx record Infer
      let body row =
            withLookupField
              ( \case
                  LookupFound x _ → do
                    selfLazy' ← fmap LazyTerm $ sendIO $ newIORef $ normalize @_ @m ctx record
                    -- TODO: This replaces `self` with the entire record.
                    -- It doesn't filter out only the accessible fields.
                    -- It's quite easy to filter by updating the lookupField, but do we need it really?
                    -- As I understand it, the inference should fail first.
                    x' ← normalize (HM.singleton (P.Ident "self") selfLazy') x
                    pure x'
                  _ → stackError "Field not found"
              )
              id
              True
              tag
              ([], Just row)
      withMono
        id
        recordTy
        ( \var → \case
            (mScope, mT) → beforeEx mScope var do
              u ← pushExVar $ Just $ P.Builtin P.U32
              row ← pushExVar $ Just $ P.rowOf $ P.typOf u
              pure do
                writeMeta (mScope, mT) var $ P.recordOf row
                body row
        )
        \case
          P.App (P.Builtin P.Record) row → body row
          _ → stackError "Not a record"
    (P.App f a, Infer) → do
      fTy ← infer ctx f Infer
      withMono
        id
        fTy
        ( \var (mScope, mT) →
            -- I'm not satisfied by this solution, but instMeta solution is
            -- even more verbose since it accepts full TermT as input.
            beforeEx mScope var do
              i ← pushExVar $ Just $ P.Builtin P.U32
              inT ← pushExVar $ Just $ P.typOf i
              outT ← pushExVar $ Just $ P.typOf i
              pure do
                writeMeta (mScope, mT) var (P.Pi Nothing inT outT)
                infer ctx a $ Check $ inT
                pure outT
        )
        \case
          P.Pi inNameM inT outT → do
            infer ctx a $ Check $ inT
            case inNameM of
              Nothing → pure outT
              Just inName → do
                a' ←
                  normalize
                    (HM.mapMaybe fst ctx)
                    a
                normalize
                  (HM.singleton inName a')
                  outT
          t → stackError $ "inferApp " <> P.pTerm 0 t
    (P.NatLit _, Infer) → pure $ P.Builtin P.U32
    (P.TagLit _, Infer) → pure $ P.Builtin P.Tag
    (P.FieldsLit P.FRecord knownVal rest, Infer) → do
      knownTy ← for knownVal \(name, val) → do
        infer ctx name $ Check $ P.Builtin P.Tag
        ty ← infer ctx val Infer
        pure (name, ty)
      rest' ← for rest \rest' → do
        restT ← infer ctx rest' Infer
        withMono
          id
          restT
          ( \var (mScope, mT) →
              beforeEx mScope var do
                u ← pushExVar $ Just $ P.Builtin P.U32
                row ← pushExVar $ Just $ P.rowOf $ P.typOf u
                pure do
                  writeMeta (mScope, mT) var $ P.recordOf row
                  pure row
          )
          \case
            P.App (P.Builtin P.Record) row → pure row
            t → stackError $ "inferRecord " <> P.pTerm 0 t
      pure $ P.recordOf $ P.FieldsLit P.FRow knownTy rest'
    (P.FieldsLit P.FRow known rest, Check (P.App (P.Builtin P.Row) ty)) → do
      let extSelf field =
            HM.adjust
              ( \case
                  (Nothing, P.App (P.Builtin P.Record) (P.FieldsLit P.FRow existing r)) →
                    (Nothing, P.recordOf $ P.FieldsLit P.FRow (field : existing) r) -- TODO: RevList? Seq?
                  _ → error "impossible"
              )
              (P.Ident "self")
      ctx' ←
        foldM
          ( \ctx' (name, val) → do
              infer ctx' name $ Check $ P.Builtin P.Tag
              infer ctx' val $ Check ty
              name' ← normalize ctx' name
              val' ← normalize ctx' val
              pure $ extSelf (name', val') ctx'
          )
          ctx
          known
      for_ rest \rest' → infer ctx' rest' $ Check $ P.rowOf ty
    (P.FieldsLit P.FRow known rest, Infer) → scoped do
      t ← pushExVar Nothing
      pure do
        infer ctx (P.FieldsLit P.FRow known rest) $ Check $ P.rowOf t
        pure $ P.rowOf t
    (P.FieldsLit P.FRecord [] restM, Check (P.App (P.Builtin P.Record) row)) →
      case restM of
        Just rest → infer ctx rest $ Check $ P.recordOf row
        Nothing → subtype (P.FieldsLit P.FRow [] Nothing) row
    (P.FieldsLit P.FRecord ((name, val) : fields) rest, Check (P.App (P.Builtin P.Record) row)) → do
      name' ← normalize ctx name
      withLookupField
        ( \case
            LookupFound ty row' → do
              infer ctx val $ Check $ ty
              val' ← normalize ctx val
              row'' ←
                normalize
                  (HM.insert (P.Ident "self") (mkFromTerm (Proxy @m) $ P.FieldsLit P.FRecord [(name', val')] Nothing) ctx)
                  $ uncurry (P.FieldsLit P.FRow) row'
              infer ctx (P.FieldsLit P.FRecord fields rest) $ Check $ P.recordOf row''
            x → stackError $ "FRecord: " <> pretty (show x)
        )
        (\_ x → x)
        True
        name
        ([], Just row)
    (P.Sorry _ x, Infer) → normalize (HM.mapMaybe fst ctx) x -- TODO: dedup
    (P.Var x, Infer) → case HM.lookup x ctx of
      Nothing → stackError $ "Unknown var " <> P.pIdent x
      Just (_, ty) → pure ty
    (P.Quantification _ name kind ty, mode) → scoped_ do
      u ← pushExVar $ Just $ P.Builtin P.U32
      pure do
        infer ctx kind $ Check $ P.typOf u
        kind' ← normalize (HM.mapMaybe fst ctx) kind
        -- TODO: investigate correctness. This allows things like:
        -- `forall x. Type -> x` : Kind
        -- TODO: ... this allows things like:
        -- /: fadeno.U32 -> fadeno.U32
        -- forall (x : fadeno.U32). (\y. x + y)
        -- ... so this is absolutely wrong, need to think about this.
        infer (HM.insert name (Nothing, kind') ctx) ty mode
    (P.Pi inNameM x y, Check (P.App (P.Builtin P.Type) u)) → do
      infer ctx x $ Check $ P.typOf u
      infer (maybe id (`HM.insert` (Nothing, x)) inNameM ctx) y $ Check $ P.typOf u
    (P.Pi inNameM x y, Infer) → scoped do
      u ← pushExVar $ Just $ P.Builtin P.U32
      pure do
        infer ctx (P.Pi inNameM x y) $ Check $ P.typOf u
        pure $ P.typOf u
    (P.Builtin x, Infer) → pure $ P.typOfBuiltin x
    (P.BuiltinsVar, Infer) → pure $ P.App (P.Builtin P.Record) $ P.FieldsLit P.FRow (fmap snd <$> P.builtinsVar) Nothing -- infer ctx P.builtinsVar Infer -- TODO: redo.
    (P.ExVar (P.ExVar' i), mode) →
      sendIO (readIORef i) >>= \case
        Left t → infer ctx t mode
        Right (_, (_, Just ty)) → case mode of
          Infer → pure ty
          Check ty2 → subtype ty ty2
        Right (_, (_, Nothing)) → stackError "Cannot infer value of existential metavariable"
    (P.UniVar _ _ t, Infer) → pure t
    (term, Check c) → stackScope ("check via infer" <+> P.pTerm 0 term <+> ":" <+> P.pTerm 0 c) do
      ty ← infer ctx term Infer
      subtype ty c

-- | a <: b
subtype ∷ ∀ sig m. (Has Solve sig m) ⇒ P.TermT → P.TermT → m ()
subtype = \a b →
  stackScope (P.pTerm 0 a <+> annotate (color Cyan) "<:" <+> P.pTerm 0 b) do
    a' ← unwrapExs a
    b' ← unwrapExs b
    subtype' (a', b')
 where
  subtype' = \case
    (aT, (P.Quantification P.Forall xName xTy bT)) → scoped_ do
      x' ← pushUniVar xTy
      pure do
        bT' ← normalize (HM.singleton xName x') bT
        subtype (aT) (bT')
    ((P.Quantification P.Exists xName xTy aT), bT) → scoped_ do
      x' ← pushUniVar xTy
      pure do
        aT' ← normalize (HM.singleton xName x') aT
        subtype (aT') (bT)
    ((P.Quantification P.Forall xName xTy aT), bT) → scoped_ do
      x' ← pushExVar $ Just xTy
      pure do
        aT' ← normalize (HM.singleton xName x') aT
        subtype (aT') (bT)
    (aT, (P.Quantification P.Exists xName xTy bT)) → scoped_ do
      x' ← pushExVar $ Just xTy
      pure do
        bT' ← normalize (HM.singleton xName x') bT
        subtype (aT) (bT')
    ((P.ExVar a), bT) → subtypeMeta a bT
    (aT, (P.ExVar b)) → subtypeMeta b aT
    ((P.UniVar a _ _), (P.UniVar b _ _))
      | a == b → pure ()
    ((P.Pi aNameM a b), (P.Pi cNameM c d)) → scoped_ do
      subtype (c) (a)
      e ← pushUniVar $ c
      pure do
        b' ← maybe pure (\aName → normalize $ HM.singleton aName e) aNameM b
        d' ← maybe pure (\cName → normalize $ HM.singleton cName e) cNameM d
        subtype (b') (d')
    -- ((P.App f1 a1), (P.App f2 a2)) → do
    --   -- TODO: not sure
    --   subtype (f1) (f2)
    --   subtype (f2) (f1)
    --   subtype (a1) (a2)
    --   subtype (a2) (a1)
    ((P.FieldsLit P.FRow _ _), (P.FieldsLit P.FRow [] Nothing)) → pure ()
    ((P.FieldsLit P.FRow [] (Just a)), b) → subtype (a) b -- TODO: What if a is not FieldsLit
    ((P.FieldsLit P.FRow fields rest), (P.FieldsLit P.FRow ((nameReq, valReq) : fieldsReq) restReq)) → do
      withLookupField
        ( \case
            LookupFound val (fields', rest') → do
              subtype val valReq
              scoped_ do
                e ← pushUniVar val
                pure do
                  let mkRest f r = normalize (HM.singleton (P.Ident "self") $ P.FieldsLit P.FRecord [(nameReq, e)] Nothing) $ P.FieldsLit P.FRow f r
                  aT ← mkRest fields' rest'
                  bT ← mkRest fieldsReq restReq
                  subtype aT bT
            _ → stackError "<: lookup unknown todo"
        )
        (\_ x → x)
        True
        nameReq
        (fields, rest)
    (P.Builtin a, P.Builtin b)
      | a == b → pure ()
    (P.App (P.Builtin P.Type) a, P.App (P.Builtin P.Type) b) → do
      a' ← unwrapExs a
      b' ← unwrapExs b
      case (a', b') of
        (P.NatLit x, P.NatLit y)
          | x <= y → pure ()
        (P.ExVar a'', _) → subtypeMeta a'' b
        (_, P.ExVar b'') → subtypeMeta b'' a
        _ → stackError $ "Cannot check that universe" <+> P.pTerm 0 a <+> "<=" <+> P.pTerm 0 b
    (P.App (P.Builtin P.Record) aT, P.App (P.Builtin P.Record) bT) → subtype aT bT
    (P.App (P.Builtin P.Row) aT, P.App (P.Builtin P.Row) bT) → subtype aT bT
    -- ((P.Row aT), (P.Row bT)) → subtype (aT) (bT)
    -- (P.U32, P.U32) → pure ()
    -- (P.Ty, P.Ty) → pure ()
    -- (P.Tag, P.Tag) → pure ()
    -- ((P.Record aT), (P.Record bT)) → subtype (aT) (bT)
    -- ((P.Row aT), (P.Row bT)) → subtype (aT) (bT)
    (aT, bT) → stackError $ P.pTerm 0 aT <+> "<:" <+> P.pTerm 0 bT
  unwrapExs ∷ P.TermT → m P.TermT
  unwrapExs inp = case inp of
    (P.Sorry _ t) → unwrapExs $ t
    (P.ExVar (P.ExVar' a)) →
      sendIO (readIORef a) >>= \case
        Left i → unwrapExs $ i
        _ → pure inp
    _ → pure inp
  subtypeMeta (P.ExVar' a) bT =
    sendIO (readIORef a) >>= \case
      Left _ → error "Impossible"
      Right (_, scope) → instMeta scope (P.ExVar' a) bT

runSolveM ∷ (Applicative m) ⇒ StateC (IntMap (RevList P.ExVar')) (FreshC (ErrorC (Doc AnsiStyle) m)) a → m (Either (Doc AnsiStyle) a)
runSolveM =
  runError (pure . Left) (pure . Right)
    . evalFresh 0
    . evalState mempty

checkFile ∷ FilePath → IO ()
checkFile file = do
  term ← P.parseFile file
  (stacks, res) ← runStackAccC $ runSolveM $ infer [] term Infer
  P.render case res of
    Left e →
      pStacks stacks
        <> line
        <> annotate (color Red) "error: "
        <> e
    Right r → P.pTerm 0 r

-- TODO: dedup
checkFileDebug ∷ FilePath → IO ()
checkFileDebug file = do
  term ← P.parseFile file
  res ← runStackPrintC $ runSolveM $ infer [] term Infer
  P.render case res of
    Left e → annotate (color Red) "error: " <> e
    Right r → P.pTerm 0 r

-- IC

data Polarity = Pos | Neg

-- data PortId (p :: Polarity) = PortId !Int
-- data WireId = WireId !Int
-- type Wire = Either (Node Neg) (Node Pos)

-- | And end of a wire.
data WireEnd (p ∷ Polarity) = WireEnd !Word32
  deriving (Show)

type AnyWireEnd = Either (WireEnd Neg) (WireEnd Pos)

data Node ∷ Polarity → Type where
  App ∷ !(WireEnd Neg) → !(WireEnd Pos) → Node Neg
  Lam ∷ !(WireEnd Pos) → !(WireEnd Neg) → Node Pos
  Dup ∷ !Word32 → !(WireEnd Pos) → !(WireEnd Pos) → Node Neg
  Sup ∷ !Word32 → !(WireEnd Neg) → !(WireEnd Neg) → Node Pos
  Word32 ∷ !Word32 → Node Pos
  Op2 ∷ !P.OpT → !(WireEnd Pos) → !(WireEnd Neg) → Node Neg
  Op1 ∷ !P.OpT → !(WireEnd Pos) → !(Word32) → Node Neg
  Era ∷ Node Neg
  Nul ∷ Node Pos
  StaticHeavy ∷ !HeavyId → !(Vector AnyWireEnd) → Node Pos
  Debug ∷ Node Neg

instance Show (Node a) where
  show = \case
    App{} → "App"
    Lam{} → "Lam"
    Dup{} → "Dup"
    Sup{} → "Sup"
    Word32{} → "Word32"
    Op2{} → "Op2"
    Op1{} → "Op1"
    Era{} → "Era"
    Nul{} → "Nul"
    StaticHeavy{} → "StaticHeavy"
    Debug{} → "Debug"

type AnyNode = Either (Node Neg) (Node Pos)

newtype HeavyId = HeavyId Word32

{- | Extension over WireEnd that also allows to serialise wires to primary ports;
wires to heavy's auxiliary ports, both persistent and temporary (the ones used for multi-operand nodes introduced by -op1-op2+>).
-}
data HeavyWireEnd (pol ∷ Polarity)
  = HWAux !(WireEnd pol)
  | HWPri !Word32

type AnyHeavyWireEnd = Either (HeavyWireEnd Neg) (HeavyWireEnd Pos)

-- Format of heavy package differs between -lang and -jit.
-- First elements of the auxs vector contains persistent aux, last — temporary ones. In normal order.
data StaticHeavyPackage = StaticHeavyPackage !Int !Bool !(HeavyWireEnd Neg) !(Vector AnyHeavyWireEnd) !(Vector AnyNode)

type Eval = State (IntMap (Either Word32 AnyNode)) :+: State (IntMap StaticHeavyPackage) :+: Fresh :+: Lift IO

newWire ∷ (Has Eval sig m) ⇒ m (WireEnd Neg, WireEnd Pos)
newWire = do
  wireId ← fromIntegral <$> fresh
  pure (WireEnd wireId, WireEnd wireId)

type family OppositePolarity a ∷ Polarity where
  OppositePolarity Pos = Neg
  OppositePolarity Neg = Pos

class DecPolarity (a ∷ Polarity) where
  decPolarity ∷ Proxy a → Either (a :~: Neg) (a :~: Pos)

instance DecPolarity Neg where
  decPolarity _ = Left Refl

instance DecPolarity Pos where
  decPolarity _ = Right Refl

travPorts ∷ (Applicative f) ⇒ (∀ b. (DecPolarity b) ⇒ WireEnd b → f (WireEnd b)) → Node a → f (Node a)
travPorts f = \case
  App a b → App <$> f a <*> f b
  Lam a b → Lam <$> f a <*> f b
  Dup dupl a b → Dup dupl <$> f a <*> f b
  Sup dupl a b → Sup dupl <$> f a <*> f b
  Word32 w → pure $ Word32 w
  Op2 op a b → Op2 op <$> f a <*> f b
  Op1 op a w → (\a' → Op1 op a' w) <$> f a
  Era → pure Era
  Nul → pure Nul
  StaticHeavy heavyId auxs → StaticHeavy heavyId <$> for auxs (either (fmap Left . f) (fmap Right . f))
  Debug → pure Debug

-- Destructive
contractWire ∷ ∀ a sig m. (DecPolarity a, Has Eval sig m) ⇒ WireEnd a → m (Word32, Maybe (Node (OppositePolarity a)))
contractWire (WireEnd wire0Id) = do
  wire0 ← IM.lookup @(Either Word32 AnyNode) (fromIntegral wire0Id) <$> get
  case wire0 of
    Just (Left wireId) → do
      modify $ IM.delete @(Either Word32 AnyNode) $ fromIntegral wire0Id
      contractWire $ WireEnd @a wireId
    Just (Right a) →
      pure
        ( wire0Id
        , Just case (a, decPolarity $ Proxy @a) of
            (Left a', Right Refl) → a'
            (Right a', Left Refl) → a'
            _ → error $ "impossible " <> show wire0Id
        )
    Nothing → pure (wire0Id, Nothing)

-- TODO: totality
link ∷ (Has Eval sig m) ⇒ WireEnd Neg → WireEnd Pos → m ()
link l0Id r0Id = do
  (lId, l) ← contractWire l0Id
  (rId, r) ← contractWire r0Id
  case (l, r) of
    (Nothing, _) → do
      modify $ IM.insert @(Either Word32 AnyNode) (fromIntegral lId) $ Left rId
    (Just _, Nothing) → do
      modify $ IM.insert @(Either Word32 AnyNode) (fromIntegral rId) $ Left lId
    (Just a, Just b) → do
      for_ @[] [lId, rId] $ modify . IM.delete @(Either Word32 AnyNode) . fromIntegral
      eval b a

move ∷ ∀ a sig m. (Has Eval sig m, DecPolarity a) ⇒ Node a → WireEnd a → m ()
move a wire0Id = do
  (wireId, wire) ← contractWire wire0Id
  case wire of
    Nothing → do
      modify $ IM.insert @(Either Word32 AnyNode) (fromIntegral wireId) $ Right $ either (\Refl → Left a) (\Refl → Right a) $ decPolarity $ Proxy @a
    Just b → do
      modify $ IM.delete @(Either Word32 AnyNode) $ fromIntegral wireId
      uncurry eval $ either (\Refl → (a, b)) (\Refl → (b, a)) $ decPolarity $ Proxy @a

newtype TupC m a = TupC (∀ (r ∷ Type). ((a, a) → m r) → m r)
  deriving (Functor)

instance Applicative (TupC m) where
  pure a = TupC \r → r (a, a)
  TupC f <*> TupC a = TupC \r →
    f \(f1, f2) → a \(a1, a2) → r (f1 a1, f2 a2)

dup ∷ ∀ a sig m. (DecPolarity a, Has Eval sig m) ⇒ WireEnd a → TupC (ReaderC Word32 m) (WireEnd a)
dup orig = TupC \r → do
  (d1, s1) ← lift newWire
  (d2, s2) ← lift newWire
  l ← ask @Word32
  case decPolarity $ Proxy @a of
    Left Refl → do
      move (Dup l s1 s2) orig
      r (d1, d2)
    Right Refl → do
      move (Sup l d1 d2) orig
      r (s1, s2)

runComm ∷ (Has Eval sig m) ⇒ Word32 → TupC (ReaderC Word32 m) a → m (a, a)
runComm l (TupC act) = runReader l $ act pure

runDup ∷ (Has Eval sig m, DecPolarity a) ⇒ Word32 → WireEnd a → WireEnd a → TupC (ReaderC Word32 m) (Node a) → m ()
runDup l dp1 dp2 act = do
  (d1, d2) ← runComm l act
  move d1 dp1
  move d2 dp2

primary ∷ ∀ a sig m. (DecPolarity a, Has Eval sig m) ⇒ Node a → m (WireEnd (OppositePolarity a))
primary n = do
  (neg, pos) ← newWire
  case decPolarity $ Proxy @a of
    Left Refl → move n neg $> pos
    Right Refl → move n pos $> neg

packHV ∷ HeavyWireEnd a → WireEnd a
packHV hv =
  let (tag, val) = case hv of
        HWAux (WireEnd v) → (0, v)
        HWPri v → (1, v)
   in -- HWPersistentAux v → (2, v)
      -- HWTemporaryAux v → (3, v)
      WireEnd $ (tag `unsafeShiftL` 31) .|. val

unpackHV ∷ WireEnd a → HeavyWireEnd a
unpackHV (WireEnd x) =
  let (tag, val) = (x `unsafeShiftR` 31, x .&. 0x7FFFFFFF)
   in case tag of
        0 → HWAux $ WireEnd val
        1 → HWPri val
        _ → error "unknown tag"

instHeavy ∷ ∀ sig m. (Has Eval sig m) ⇒ HeavyId → Vector AnyWireEnd → m (WireEnd Neg)
instHeavy (HeavyId heavyId) auxs = do
  StaticHeavyPackage persAuxsLen hasResAux mainWire auxWires ns ← P.fromJust . IM.lookup @StaticHeavyPackage (fromIntegral heavyId) <$> get
  let write ∷ ∀ a. (DecPolarity a) ⇒ Word32 → StateC (IntMap Word32) m (Node a)
      write i = case (decPolarity $ Proxy @a, P.fromJust $ ns V.!? fromIntegral i) of
        (Left Refl, Left n) → travPorts r n
        (Right Refl, Right n) → travPorts r n
        _ → error "impossible"

      r ∷ ∀ a. (DecPolarity a) ⇒ WireEnd a → StateC (IntMap Word32) m (WireEnd a)
      r = r' . unpackHV

      r' ∷ ∀ a. (DecPolarity a) ⇒ HeavyWireEnd a → StateC (IntMap Word32) m (WireEnd a)
      r' hw0 = case hw0 of
        HWAux (WireEnd wire0Id) → do
          wireIdM ← IM.lookup (fromIntegral wire0Id) <$> get
          WireEnd <$> case wireIdM of
            Nothing → do
              wireId ← fresh
              modify $ IM.insert @Word32 (fromIntegral wire0Id) $ fromIntegral wireId
              pure $ fromIntegral wireId
            Just wireId → do
              modify $ IM.delete @Word32 $ fromIntegral wire0Id
              pure wireId
        HWPri nodeId →
          either (\Refl → primary =<< write @Pos nodeId) (\Refl → primary =<< write @Neg nodeId) $ decPolarity $ Proxy @a
  evalState IM.empty do
    for_ (V.zip auxs auxWires) \case
      (Left ext, Right int) → link ext =<< r' int
      (Right ext, Left int) → (`link` ext) =<< r' int
      _ → error "impossible"
    r' mainWire

eval ∷ (Has Eval sig m) ⇒ Node Neg → Node Pos → m ()
eval = curry \case
  (Era, b) →
    void
      $ travPorts
        ( \(a ∷ WireEnd b) → case decPolarity $ Proxy @b of
            Left Refl → move Era a $> WireEnd 0
            Right Refl → move Nul a $> WireEnd 0
        )
        b
  (Dup dupl dp1 dp2, Sup supl tm1 tm2)
    | dupl == supl → do
        link tm1 dp1
        link tm2 dp2
  (Dup dupl dp1 dp2, b) → runDup dupl dp1 dp2 $ travPorts dup b
  (a, Sup supl tm1 tm2) → runDup supl tm1 tm2 $ travPorts dup a
  (a, StaticHeavy heavyId auxs) → move a =<< instHeavy heavyId auxs
  (App arg ret, Lam var bod) → do
    link arg var
    link bod ret
  (App arg ret, Nul) → move Era arg *> move Nul ret
  (App{}, _) → wrong
  (Op2 op ret other, Word32 w) → move (Op1 op ret w) other
  (Op2 _ ret other, Nul) → move Nul ret *> move Era other
  (Op2{}, _) → wrong
  (Op1 op ret w1, Word32 w2) →
    let op' = case op of
          P.Add → (+)
          P.Sub → (-)
          P.Mul → (*)
          P.Div → div
     in move (Word32 $ op' w1 w2) ret
  (Op1 _ ret _, Nul) → move Nul ret
  (Op1{}, _) → wrong
  (Debug, Word32 x) → do
    sendIO $ print x
    pure ()
  (Debug, _) → wrong
 where
  wrong = error "wrong interaction"

newtype FreeVars = FreeVars {unFreeVars ∷ HashMap P.Ident (NonEmpty (WireEnd Pos))}

instance Semigroup FreeVars where
  FreeVars a <> FreeVars b = FreeVars $ HM.unionWith (<>) a b

instance Monoid FreeVars where
  mempty = FreeVars mempty

catchFree ∷ (Has (Writer FreeVars) sig m) ⇒ P.Ident → m a → m ([WireEnd Pos], a)
catchFree name act =
  censor @FreeVars (FreeVars . HM.delete name . unFreeVars)
    $ (bimap (maybe [] toList . HM.lookup name . unFreeVars) id)
    <$> listen @FreeVars act

shareBetween ∷ (Has Eval sig m) ⇒ [WireEnd Pos] → m (WireEnd Pos)
shareBetween = \case
  [] → primary Era
  [x] → pure x
  x : xs@(_ : _) → do
    f ← fresh -- TODO: use separate fresh
    primary . Dup (fromIntegral f) x =<< shareBetween xs

isAffine ∷ [a] → Bool
isAffine = \case
  [] → True
  [_] → True
  _ : _ : _ → False

-- Doesn't contract wires so is not performant at all.
isPrimary ∷ (Has Eval sig m) ⇒ WireEnd a → m Bool
isPrimary (WireEnd wire0Id) = do
  wire ← IM.lookup @(Either Word32 AnyNode) (fromIntegral wire0Id) <$> get
  case wire of
    Just (Left x) → isPrimary $ WireEnd $ fromIntegral x
    Just (Right _) → pure True
    Nothing → pure False

whilePop ∷ ∀ a sig m. (Has (State (Seq a)) sig m) ⇒ (a → m ()) → m ()
whilePop f =
  get @(Seq a) >>= \case
    (a :<| as) → put as *> f a *> whilePop f
    _ → pure ()

-- TODO: contract & retartget auxsList
-- deferred?
mkHeavy ∷ ∀ sig m. (Has Eval sig m) ⇒ WireEnd Neg → Vector AnyWireEnd → m StaticHeavyPackage
mkHeavy = \main0 auxs0 → do
  (pkg, (ma, au)) ← runWriter @(RevList AnyNode) (curry pure) $ evalState @Word32 0 $ evalState @(Seq AnyNode) mempty do
    m ← hdlPort' main0
    a ← for auxs0 $ either (fmap Left . hdlPort') (fmap Right . hdlPort')
    whilePop hdlNode
    pure (m, a)
  pure $ StaticHeavyPackage (V.length au) False ma au $ fromList $ toList pkg
 where
  -- auxsLen = length auxsList
  hdlNode ∷ ∀ sig2 m2. (Has (Eval :+: State Word32 :+: State (Seq AnyNode) :+: Writer (RevList AnyNode)) sig2 m2) ⇒ AnyNode → m2 ()
  hdlNode origN = do
    n ← either (fmap Left . travPorts hdlPort) (fmap Right . travPorts hdlPort) origN
    tell @(RevList AnyNode) [n]
  hdlPort ∷ ∀ a sig2 m2. (Has (Eval :+: State Word32 :+: State (Seq AnyNode)) sig2 m2) ⇒ (DecPolarity a) ⇒ WireEnd a → m2 (WireEnd a)
  hdlPort = fmap packHV . hdlPort'
  hdlPort' ∷ ∀ a sig2 m2. (Has (Eval :+: State Word32 :+: State (Seq AnyNode)) sig2 m2) ⇒ (DecPolarity a) ⇒ WireEnd a → m2 (HeavyWireEnd a)
  hdlPort' wire0Id = do
    (wireId, thisM) ← contractWire wire0Id
    case thisM of
      Nothing → pure $ HWAux $ WireEnd wireId
      Just this → do
        modify @(Seq AnyNode) $ \q → q :|> either (\Refl → Right this) (\Refl → Left this) (decPolarity $ Proxy @a)
        state @Word32 \len → (len + 1, HWPri len)

{-

First of all, *I want Unicode*, but that's going to kill us I'm afraid.

Terms constructs of my abomination:
  forall X | T — impedicative quantification (`forall` from Fall From Grace)
  forall x : T | T' — type for erased lambdas.
  ** X : T | T' — type for dependent functions.
  \x y — a lambda
  \x A — a type for dependent function
-}

useFreeVar ∷ (Has (Writer FreeVars :+: Eval) sig m) ⇒ P.Ident → m (WireEnd Neg)
useFreeVar ident = do
  (n, p) ← newWire
  tell $ FreeVars $ HM.singleton ident (p :| [])
  pure n

compile ∷ (Has (Writer FreeVars :+: Eval) sig m) ⇒ P.TermT → m (WireEnd Neg)
compile = \case
  -- P.Node captures pos val → do
  --   (freesInBod, val') ← intercept @FreeVars $ compile val
  --   -- Just compile into a heavy package, failing if free vars mismatch.
  --   -- The resulting heavy package
  --   undefined
  P.Block (P.BlockLet name _ val) bod → do
    (occInBod, bod') ← catchFree name $ compile bod
    case occInBod of
      [] → pure ()
      _ → do
        (freesInVal, val') ← intercept @FreeVars $ compile val
        val'' ← runEmpty
          do
            -- fallback
            tell freesInVal
            pure val'
          pure
          do
            E.guard $ sum (length <$> unFreeVars freesInVal) <= 8 -- Cannot package when >8 auxs.
            E.guard =<< isPrimary val'
            let auxs = toList (unFreeVars freesInVal) >>= \(n, l) → (n,) <$> toList l
            for_ auxs \(_, aux) → E.guard . not =<< isPrimary aux
            -- Wrap
            heavyPackage ← mkHeavy val' (fromList $ Right . snd <$> auxs)
            heavyId ← fresh
            modify $ IM.insert heavyId heavyPackage

            primary =<< StaticHeavy (HeavyId $ fromIntegral heavyId) . fromList <$> for auxs \(i, _) → Left <$> useFreeVar i
        link val'' =<< shareBetween occInBod
    pure bod'
  P.Lam arg bod → do
    (occ, bod') ← catchFree arg $ compile bod
    occ' ← shareBetween occ
    primary $ Lam occ' bod'
  P.Op a op b → do
    a' ← compile a
    b' ← compile b
    (retn, retp) ← newWire
    move (Op2 op retp b') a'
    pure retn
  P.App f x → do
    f' ← compile f
    x' ← compile x
    (retn, retp) ← newWire
    move (App x' retp) f'
    pure retn
  P.NatLit x → primary $ Word32 x
  P.Var ident → useFreeVar ident

data Sizing a = SizeNul | SizeInline !Word32 | Size !a
  deriving (Functor)

-- | Returns total size in dwords and amount of data slots.
sizing ∷ Node a → Sizing (Word8, Word8)
sizing = \case
  App{} → j 2 0
  Lam{} → j 2 0
  Dup{} → j 2 0
  Sup{} → j 2 0
  Word32 l → SizeInline l
  Op2{} → j 2 0
  Op1{} → j 2 1
  Era → SizeNul
  Nul → SizeNul
  StaticHeavy _ auxs → Size (fromIntegral $ V.length auxs + 1, 1)
  Debug → SizeNul
 where
  j a b = Size (a, b)

packW16 ∷ (Word8, Word8) → Int
packW16 (a, b) = (fromIntegral a `unsafeShiftL` 8) .|. fromIntegral b

unpackW16 ∷ Int → (Word8, Word8)
unpackW16 x = (fromIntegral $ x `unsafeShiftR` 8, fromIntegral x)

-- | Returns subpacks and position of each input node in the respective subpack.
serPartitionSubpacks ∷ Vector AnyNode → (IntMap (Word32, RevList AnyNode), Vector Word32)
serPartitionSubpacks nodes = runIdentity
  $ runState @(IntMap (Word32, RevList AnyNode)) (curry pure) mempty
  $ for nodes \node →
    either sizing sizing node & \case
      Size s →
        state @(IntMap (Word32, RevList AnyNode)) \subpacks →
          let subpackId = packW16 s
              (oldSize, oldMembers) = fromMaybe (0, []) $ IM.lookup subpackId subpacks
           in (IM.insert subpackId (oldSize + 1, oldMembers `revSnoc` node) subpacks, oldSize)
      _ → pure 0

-- | Returns packs (each containing subpacks) and position of each input node.
serPartitionPacks ∷ Vector AnyNode → (IntMap (Word32, RevList (Word8, Word32, RevList AnyNode)), Word32 → Sizing (Word8, Word32))
serPartitionPacks nodes =
  let (subpacks, nodeOffsetInSubpack) = serPartitionSubpacks nodes
      (packs, subpackOffsetInPack) = runIdentity $ runState (curry pure) mempty $ flip IM.traverseWithKey subpacks \(unpackW16 → (packId, datas)) (size, subpack) →
        state @(IntMap (Word32, RevList (Word8, Word32, RevList AnyNode))) \oldPacks →
          let (oldPackSize, oldPackSubpacks) = fromMaybe (0, mempty) $ IM.lookup (fromIntegral packId) oldPacks
           in (IM.insert (fromIntegral packId) (oldPackSize + size, oldPackSubpacks `revSnoc` (datas, size, subpack)) oldPacks, oldPackSize)
   in ( packs
      , \nodeId →
          either sizing sizing (P.fromJust (nodes V.!? fromIntegral nodeId))
            <&> \(packId, subpackId) →
              ( packId
              , P.fromJust (IM.lookup (fromIntegral $ packW16 (packId, subpackId)) subpackOffsetInPack)
                  + P.fromJust (nodeOffsetInSubpack V.!? fromIntegral nodeId)
              )
      )

type HeavySerM = StateC Word32 (StateC (RevList (Word32, HeavyId)) (LiftC PutM))

serW32 ∷ Word32 → HeavySerM ()
serW32 x = do
  modify @Word32 (+ 1)
  sendM $ putWord32be x

serW64 ∷ Word64 → HeavySerM ()
serW64 x = do
  modify @Word32 (+ 2)
  sendM $ putWord64be x

serTravSlots_ ∷ ∀ f a. (Applicative f) ⇒ (Word8 → Either AnyHeavyWireEnd (HeavySerM ()) → f ()) → Node a → f ()
serTravSlots_ f = \case
  App a b → p 0 a *> p 1 b
  Lam a b → p 0 a *> p 1 b
  Dup _ a b → p 0 a *> p 1 b
  Sup _ a b → p 0 a *> p 1 b
  Word32 _ → pure ()
  Op2 _ a b → p 0 a *> p 1 b
  Op1 _ a b → p 0 a *> f 1 (Right $ serW64 $ fromIntegral b)
  Era → pure ()
  Nul → pure ()
  StaticHeavy heavyId b →
    sequenceA_ (zipWith (\i → either (p i) (p i)) [0 ..] $ toList b)
      *> f
        (fromIntegral $ V.length b)
        ( Right do
            pos ← get @Word32
            modify $ (`revSnoc` (pos, heavyId))
            serW64 0
        )
  Debug → pure ()
 where
  p ∷ ∀ b. (DecPolarity b) ⇒ Word8 → WireEnd b → f ()
  p i = f i . Left . either (\Refl → Left . unpackHV) (\Refl → Right . unpackHV) (decPolarity (Proxy @b))

serHdlWires ∷ Vector AnyNode → IntMap (Word32, Word8)
serHdlWires = \nodes → runIdentity $ execWriter $ flip V.imapM_ nodes \nodeId →
  let f ∷ Node a → WriterC (IntMap (Word32, Word8)) Identity ()
      f = serTravSlots_ \portId → \case
        Left (Right (HWAux (WireEnd wire))) →
          tell $ IM.singleton (fromIntegral wire) (fromIntegral nodeId ∷ Word32, portId)
        _ → pure ()
   in either f f

packMeta ∷ Word8 → Word32 → Word32
packMeta a b = (fromIntegral a `unsafeShiftL` 24) .|. b

serMeta ∷ Node a → Word32
serMeta =
  uncurry packMeta . \case
    App{} → (4, 0)
    Lam{} → (4, 0)
    Dup l _ _ → (5, l)
    Sup l _ _ → (5, l)
    Word32 _ → (6, 0)
    Op2 op _ _ → (7, serOp op)
    Op1 op _ _ → (8, serOp op)
    Era → (3, 0)
    Nul → (3, 0)
    StaticHeavy _ x → (10, fromIntegral $ V.length x)
    Debug → (100, 0)
 where
  serOp ∷ P.OpT → Word32
  serOp = \case
    P.Add → 0
    P.Sub → 1
    P.Mul → 2
    P.Div → 3

serHeavy ∷ StaticHeavyPackage → PutM (RevList (Word32, HeavyId))
serHeavy (StaticHeavyPackage _hpersAux _hspecRes hmain0 hauxs hnodes) = do
  let auxForWire = serHdlWires hnodes
  let (packs, nodeIdToPos) = serPartitionPacks hnodes
  let packToVirt = IM.fromList $ zip (IM.keys packs) [0 ..]
  let ((subst, res_val_size), res_val) = runPutMBuilder $ runM $ runState (curry pure) [] $ execState 0 do
        for_ packs \(packSize, _subpacks) → serW32 packSize
        let mkRef (a ∷ Word8) (b ∷ Word32) (c ∷ Word8) = (P.fromJust (IM.lookup (fromIntegral a) packToVirt) `unsafeShiftL` 29) .|. (b `unsafeShiftL` 3) .|. fromIntegral c
            varFor (wireId ∷ Word32) =
              let (ab, c) = P.fromJust $ IM.lookup (fromIntegral wireId) auxForWire
               in case nodeIdToPos ab of
                    Size (a, b) → mkRef a b c
                    _ → error "impossible"
            serPort ∷ ∀ a. (DecPolarity a) ⇒ HeavyWireEnd a → HeavySerM ()
            serPort = \case
              HWAux (WireEnd a) → either (\Refl → serW32 (packMeta 1 0) *> serW32 (varFor a)) (\Refl → serW32 (packMeta 2 0)) $ decPolarity $ Proxy @a
              HWPri nodeId → do
                serW32 $ either serMeta serMeta $ P.fromJust $ hnodes V.!? fromIntegral nodeId
                case nodeIdToPos nodeId of
                  SizeNul → pure ()
                  SizeInline x → serW32 x
                  Size (a, b) → serW32 $ mkRef a b 0
        for_ packs \(_packSize, toList → subpacks) →
          for_ subpacks \(datas, num, toList → nodes) → do
            serW32 $ (fromIntegral datas `unsafeShiftL` 29) .|. num
            let f = serTravSlots_ \_ → \case
                  Left x → either serPort serPort x
                  Right x → x
            for_ nodes $ either f f
        serPort hmain0
        for_ hauxs $ either serPort serPort
  putWord32be res_val_size
  putWord32be $ fromIntegral $ foldr (\k acc → (acc `unsafeShiftL` 4) .|. k) 0 $ IM.keys packs
  putWord8 $ foldr (\k acc → (acc `unsafeShiftL` 1) .|. either (const 0) (const 1) k) 0 $ hauxs
  putWord8 $ fromIntegral $ IM.size packs
  putBuilder res_val
  pure subst

serHeavyRec ∷ StaticHeavyPackage → EvalC LByteString
serHeavyRec rootHeavy = fmap toLazyByteString $ evalState (S.empty @HeavyId) $ evalAccum (IM.empty @Word32) $ execWriter @Builder do
  let ser h = do
        let (UnsafeRevList subst, res) = runPutMBuilder $ serHeavy h
        tell res
        tell $ execPut $ putWord32be $ fromIntegral $ length subst -- sorry
        for_ subst \(pos, HeavyId heavyId) → do
          heavyIdToVirtId ← look
          virtId ← case IM.lookup (fromIntegral heavyId) heavyIdToVirtId of
            Nothing → do
              let v = fromIntegral $ IM.size heavyIdToVirtId
              add $ IM.singleton (fromIntegral heavyId) v
              modify $ (:|> HeavyId heavyId)
              pure v
            Just v → pure v
          tell $ execPut $ putWord32be pos *> putWord32be virtId
  ser rootHeavy
  whilePop \(HeavyId heavyId) → do
    heavy ← P.fromJust . IM.lookup (fromIntegral heavyId) <$> get
    ser heavy

type EvalC a = StateC (IntMap (Either Word32 AnyNode)) (StateC (IntMap StaticHeavyPackage) (FreshC IO)) a

runEvalC ∷ EvalC a → IO a
runEvalC = evalFresh 0 . evalState IM.empty . evalState IM.empty

compileFile ∷ FilePath → EvalC (WireEnd Neg)
compileFile fileName = do
  parsed ← sendIO $ P.parseFile fileName
  runWriter @FreeVars
    ( \(FreeVars frees) res → do
        unless (HM.null frees)
          $ error
          $ "Unknown identifiers: "
          <> intercalate ", " (show . P.pIdent . fst <$> toList frees)
        pure res
    )
    $ compile parsed

compileFileRun ∷ FilePath → EvalC ()
compileFileRun fileName = compileFile fileName >>= move Debug

compileFileToFile ∷ FilePath → IO ()
compileFileToFile file = runEvalC do
  pri ← compileFile (file <> ".fad")
  root ← mkHeavy pri []
  fadobj ← serHeavyRec root
  writeFileBinary (file <> ".fadobj") $ toStrictBytes fadobj

main ∷ IO ()
main = pure ()
