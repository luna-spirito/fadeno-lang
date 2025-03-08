{-# LANGUAGE UndecidableInstances #-}

module Main where

import Control.Algebra
import Control.Carrier.Accum.Church (evalAccum)
import Control.Carrier.Empty.Church (runEmpty)
import Control.Carrier.Error.Church (ErrorC, runError)
import Control.Carrier.Fresh.Church (FreshC, evalFresh)
import Control.Carrier.Lift (LiftC, runM)
import Control.Carrier.Reader (ReaderC, runReader)
import Control.Carrier.State.Church (StateC, evalState)
import Control.Carrier.Writer.Church (WriterC, execWriter, runWriter)
import Control.Effect.Accum (add, look)
import Control.Effect.Empty qualified as E
import Control.Effect.Error (Error, Throw, throwError)
import Control.Effect.Fresh (Fresh, fresh)
import Control.Effect.Lift (Lift, sendIO, sendM)
import Control.Effect.Reader (Reader, ask, local)
import Control.Effect.State (State, get, modify, state)
import Control.Effect.Writer (Writer, censor, listen, tell)
import Data.Bits (unsafeShiftL, unsafeShiftR, (.&.), (.|.))
import Data.ByteString.Builder (toLazyByteString)
import Data.ByteString.Char8 qualified as BS
import Data.IntMap.Strict qualified as IM
import Data.Kind (Type)
import Data.List (intercalate, uncons, (!?))
import Data.Serialize (PutM, execPut, putBuilder, putWord32be, putWord64be, putWord8, runPutMBuilder)
import GHC.Exts (IsList (..))
import Normalize (EqRes (..), NormCtx (..), isEq, normalize, parseBQQ)
import Parser (BlockT (..), BuiltinT (..), ExVar' (..), Fields (..), Ident (..), Quantifier (..), RevList (..), TermT (..), builtinsList, identOfBuiltin, nested, nested', pIdent, pTerm', parseFile, recordOf, render, revSnoc, revUnsnoc, rowOf, typOf)
import Prettyprinter (Doc, Pretty, annotate, indent, line, nest, pretty, (<+>))
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
      sendIO $ render $ indent (level * 2) $ "├ " <> msg

runStackPrintC ∷ (Has (Lift IO) sig m) ⇒ StackPrintC m a → m a
runStackPrintC = runReader 0 . unStackPrintC

-- Check

data LazyTermT m = LazyTerm !(IORef (m TermT)) | LazyPure !TermT

-- instance (Has Solve sig m) ⇒ HasTerm m (LazyTermT m) where
--   extractTerm (LazyTerm var) = do
--     val ← join $ sendIO $ readIORef var
--     sendIO $ writeIORef var $ pure val
--     pure $ Just val
--   extractTerm (LazyPure x) = pure $ Just x
--   mkFromTerm _ = LazyPure

-- | Context stores values and the type of introduced bindings.
type CtxT = RevList (Maybe TermT, TermT) -- Actually stores just Idents, but VarT for easier conversion.

-- | For meta-variables
type Solve = State (RevList (RevList ExVar')) :+: Fresh :+: Error (Doc AnsiStyle) :+: StackLog :+: Lift IO

freshIdent ∷ (Has Solve sig m) ⇒ m Ident
freshIdent = UIdent <$> fresh

-- Probably access to Solve should be restricted in ExVarPushC...
-- First Int is the target scope, second (typically = 0) is the current scope
type ExVarPushC m = ReaderC Int (WriterC (RevList ExVar') m)

-- `Maybe TermT` is absolute.
pushExVar ∷ (Has (Writer (RevList ExVar') :+: Reader Int :+: Solve) sig m) ⇒ Maybe TermT → m TermT
pushExVar t = do
  scope ← ask
  name ← freshIdent
  metaVar' ← fmap ExVar' $ sendIO $ newIORef $ Right (name, nested (-scope) <$> t)
  tell @(RevList _) [metaVar']
  let res = ExVar metaVar' scope
  stackLog $ "intro" <+> pTerm' res
  pure res

pushUniVar ∷ (Has (Reader Int :+: Solve) sig m) ⇒ TermT → m TermT
pushUniVar ty = do
  stackLog $ pTerm' ty
  -- Pushed ephemerally.
  scope ← ask
  ident ← freshIdent
  let res = UniVar ident scope ty
  stackLog $ "intro" <+> pTerm' res
  pure res

-- I hate this.
revInsertBefore ∷ ∀ a. RevList a → (a → Bool) → RevList a → RevList a
revInsertBefore ins f orig = go orig
 where
  go = \case
    UnsafeRevList [] → error $ "impossible"
    UnsafeRevList (x : xs)
      | f x → [x] <> ins <> (UnsafeRevList xs)
      | otherwise →
          let (UnsafeRevList xs') = go $ UnsafeRevList xs
           in UnsafeRevList $ x : xs'

adjustList ∷ (a → a) → Int → [a] → [a]
adjustList f 0 (x : xs) = f x : xs
adjustList f n (x : xs) = x : adjustList f (n - 1) xs
adjustList _ _ [] = error "impossible"

beforeEx ∷ (Has Solve sig m) ⇒ Int → ExVar' → (ExVarPushC m (m a)) → m a
beforeEx scope ex act = do
  resM ← stackScope ("before " <> pTerm' (ExVar ex scope)) do
    (inserted, resM) ← runWriter (curry pure) $ runReader scope act
    stackLog . pretty . show =<< get @(RevList (RevList ExVar'))
    modify $ UnsafeRevList . adjustList (revInsertBefore inserted (== ex) . traceShowId . traceShow (pTerm' (ExVar ex scope))) scope . unUnsafeRevList
    pure resM
  resM

scoped' ∷ (Has Solve sig m) ⇒ ((TermT → TermT) → a → a) → ExVarPushC m (m a) → m a
scoped' tmap act = do
  tyM ← stackScope "scoped" do
    (origExs, tyM) ← runWriter (curry pure) $ runReader 0 act
    modify (`revSnoc` origExs)
    pure tyM
  ty ← tyM
  UnsafeRevList exs ←
    state @(RevList (RevList ExVar'))
      $ fromMaybe (error "Internal error: scope disappeared")
      . revUnsnoc
  snd
    <$> foldM
      ( \(i, ty') (ExVar' x) →
          sendIO (readIORef x) >>= \case
            Left t → stackError $ "Internal error: Resolved existential wasn't marked as such:" <+> pTerm' t
            Right (_, xTyM) → do
              variable ← fresh
              let variable' = Ident $ BS.pack $ "/" <> show variable
              -- [0] -> forall. $0
              -- \$0 + [0] -> forall. $1 + $0
              -- \$1 $0 (\ $0 + [1]) -> forall. $2 $1 (\ $0 + $1)
              sendIO $ writeIORef x $ Left $ Var i
              (\(ip, f) → (i + ip, f `tmap` ty')) <$> case xTyM of
                Just xTy →
                  pure $ (1, Quantification Forall variable' (nested (-i - 1) xTy) . nested' 1 1)
                Nothing → do
                  n ← freshIdent
                  pure
                    ( 2
                    , Quantification Forall n (Builtin U32)
                        . Quantification Forall variable' (typOf $ Var 0)
                        . nested' 2 1
                    )
      )
      (0, ty)
      exs

{-
pushExVarInto :: (Has Solve sig m) => Int -> Maybe TermT -> m ExVar'
pushExVarInto scope t = do
  name <- freshIdent
  metaVar' <- fmap ExVar' $ sendIO $ newIORef $ Right $ (name, (scope, t))
  insMeta scope metaVar'
  pure metaVar'

pushExVar :: (Has Solve sig m) => Maybe TermT -> m TermT
pushExVar t = do
  scope <- (\x -> x - 1) . IM.size <$> get @(IntMap [ExVar'])
  pushExVarInto scope t

scoped :: (Has Solve sig m) => m TermT -> m TermT
scoped = scoped' id
-- scoped act = do

insMeta :: (Has Solve sig m) => Int -> ExVar' -> m ()
insMeta scope var = do
  modify @(IntMap [ExVar']) \scopes ->
    IM.adjust (var :) scope scopes
-}

-- Assumes that all existentias are resolved if they are ever used.
scoped_ ∷ (Has Solve sig m) ⇒ ExVarPushC m (m a) → m a
scoped_ act = do
  -- Bad copy-pasta
  (origExs, tyM) ← runWriter (curry pure) $ runReader 0 act
  modify $ (`revSnoc` origExs)
  ty ← tyM
  modify $ fst . fromMaybe (error "Scope disappeared") . revUnsnoc @(RevList ExVar')
  pure ty

scoped ∷ (Has Solve sig m) ⇒ ExVarPushC m (m TermT) → m TermT
scoped = scoped' id

markSolved ∷ (Has Solve sig m) ⇒ Int → ExVar' → m ()
markSolved scope var = do
  modify @(RevList (RevList ExVar'))
    $ UnsafeRevList
    . adjustList
      (\(UnsafeRevList l) → UnsafeRevList $ filter (/= var) l)
      scope
    . unUnsafeRevList

-- Writes & checks
-- Writes *absolute* value to meta.
-- TODO: Check that the value is actually writeable and causes no overflows.
writeMeta ∷ (Has Solve sig m) ⇒ (Int, Maybe TermT) → ExVar' → TermT → m ()
writeMeta (scope, tyM) (ExVar' var) absVal = do
  stackLog $ "refine " <> pTerm' (ExVar (ExVar' var) scope) <+> "=" <+> pTerm' absVal
  let relVal = nested (-scope) absVal
  for_ tyM $ infer [] relVal . Check
  sendIO $ writeIORef var $ Left relVal
  markSolved scope (ExVar' var)

-- TODO: So, return the proper ordering, but just use
-- TODO: Decipher what previous TODO is supposed to mean
-- Instantiates meta with *absolute* value.
instMeta ∷ ∀ sig m. (Has Solve sig m) ⇒ (Int, Maybe TermT) → ExVar' → TermT → m ()
instMeta = (\f a b c → stackScope "instMeta" $ f a b c) \(scope1, t1) origVar1 →
  -- TODO: avoid nested?
  -- Accepts and returns absolute
  let instMeta' ∷ TermT → m TermT
      instMeta' = \case
        Sorry _ x → instMeta' x
        ExVar (ExVar' var2) scope2 →
          sendIO (readIORef var2) >>= \case
            Left t → instMeta' t
            Right (_, t2) → do
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
                              | x == ExVar' var2 → False
                              | otherwise → go xs
                            _ → error "Imposible"
                      UnsafeRevList exs ← P.fromJust . (!? scope1) . unUnsafeRevList <$> get
                      pure $ go exs
              if var2Earlier
                then pure $ ExVar (ExVar' var2) scope2
                else beforeEx scope1 origVar1 do
                  var1R ← pushExVar t2
                  pure do
                    writeMeta (scope2, t2) (ExVar' var2) var1R
                    pure var1R
        uni@(UniVar _ scope2 _)
          | scope2 <= scope1 → pure uni
        App f a → App <$> instMeta' f <*> instMeta' a
        FieldsLit FRow known rest →
          FieldsLit FRow
            <$> for known (\(a, b) → (a,) <$> instMeta' b)
            <*> for rest instMeta'
        Var x → pure $ Var x -- TODO: I hope this is correct, but needs to be rechecked.
        Builtin x → pure $ Builtin x
        NatLit x → pure $ NatLit x
        Pi inNameM inT outT → Pi inNameM <$> instMeta' inT <*> instMeta' outT
        Op a op b → do
          a' ← instMeta' a
          b' ← instMeta' b
          pure $ Op a' op b'
        x → stackError $ "instMeta (of" <+> pretty scope1 <> ")" <+> pTerm' x
   in \val →
        let r = writeMeta (scope1, t1) origVar1 =<< instMeta' val
         in case val of
              ExVar (ExVar' var2) scope2 →
                if origVar1 == ExVar' var2 && scope1 == scope2
                  then pure ()
                  else
                    sendIO (readIORef var2) >>= \case
                      Left val' → instMeta (scope1, t1) origVar1 val'
                      _ → r
              _ → r

withMono ∷ (Has Solve sig m) ⇒ ((TermT → TermT) → a → a) → TermT → (ExVar' → (Int, Maybe TermT) → m a) → (TermT → m a) → m a
withMono tmap = \a onMeta onOther → withMono' onMeta onOther a
 where
  withMono' onMeta onOther = \case
    Sorry _ v → withMono' onMeta onOther v
    ExVar (ExVar' var) nesting →
      sendIO (readIORef var) >>= \case
        Left v → withMono' onMeta onOther $ nested nesting v
        Right (_, v) → onMeta (ExVar' var) (nesting, v)
    Quantification Forall _name kind v → scoped' tmap do
      ty ← pushExVar $ Just kind
      pure $ withMono' onMeta onOther =<< normalize (NormRewrite (Var 0) ty) v
    Quantification Exists _name kind v → scoped' tmap do
      ty ← pushUniVar kind
      pure $ withMono' onMeta onOther =<< normalize (NormRewrite (Var 0) ty) v
    r → onOther r

data LookupRes
  = LookupFound !(TermT) !([(TermT, TermT)], Maybe TermT)
  | LookupMissing
  | LookupUnknown
  deriving (Show)

tmapLookupRes ∷ (TermT → TermT) → LookupRes → LookupRes
tmapLookupRes f = \case
  LookupFound a b → LookupFound (f a) b
  x → x

-- Lookups in FRow. **FRow**.
-- The type is too restrictive about requiring a continuation.
withLookupField ∷ (Has Solve sig m) ⇒ (LookupRes → m a) → ((TermT → TermT) → a → a) → Bool → TermT → ([(TermT, TermT)], Maybe TermT) → m a
withLookupField cont f refine needle = rec []
 where
  notARow x = stackError $ "Not a row:" <+> pTerm' x
  rec prev = \case
    ([], Nothing) → cont LookupMissing
    ([], Just next) → withMono
      f
      next
      ( \var →
          if refine
            then \case
              (mScope, Just (App (Builtin Row) mT)) →
                beforeEx mScope var do
                  rest' ← pushExVar (Just $ rowOf mT)
                  val' ← pushExVar (Just mT)
                  writeMeta (mScope, Just $ rowOf mT) var $ FieldsLit FRow [(needle, val')] $ Just rest'
                  pure $ cont $ LookupFound val' (toList prev, Just rest')
              (mScope, _) → notARow $ ExVar var mScope
            else const $ cont LookupMissing
      )
      \case
        FieldsLit FRow vals rest → rec prev (vals, rest)
        x → stackError $ "lookupField todo " <> pTerm' x
    ((name, val) : xs, rest) →
      isEq needle name >>= \case
        EqYes → cont $ LookupFound val (toList prev <> xs, rest)
        EqUnknown → cont LookupUnknown
        EqNot → rec (prev `revSnoc` (name, val)) (xs, rest)

{-
-- TODO: implement rewrite as a normalize subroutine.
-- Rewrites are performed on normalized terms.
-- This makes sense only since current stupid implementation rewrites
-- only the normalized bindings in scope.
-- TODO: rewrite as a form of normalize.
-- rewrite :: forall sig m. (Has Solve sig m) => (TermT, TermT) -> TermT -> m TermT
-- rewrite (what, with) = rewrite'
--   where
--     rewrite' :: TermT → m TermT
--     rewrite' curr = do
--       matches <- isEq what curr
--       case matches of
--         EqYes -> pure with
--         _ -> rec curr
--     -- TODO: This just recurses 1 level into the structure.
--     -- Probably could be deduplicated with instMeta.
--     rec :: TermT → m TermT
--     rec = \case
--       Block {} -> undefined
--       Lam argName bod -> scoped_ do
--         arg ← pushUniVar' undefined
--         pure do
--           bod' ← normalize (HM.singleton argName $ Var arg) bod
--           bodR ← rewrite' bod'
--           normalize (HM.singleton arg (Var $ SourceVar argName)) bodR
--       Op a op b → Op <$> rewrite' a <*> pure op <*> rewrite' b
--       App f a → App <$> rewrite' f <*> rewrite' a
--       x@(NatLit _) → pure x
--       x@(TagLit _) → pure x
--       FieldsLit f t v → --FildsLit f <$> _ <*> _
-}

typOfBuiltin ∷ BuiltinT → TermT
typOfBuiltin =
  \case
    U32 → [parseBQQ| Type+ 0 |]
    Tag → [parseBQQ| Type+ 0 |]
    Row → [parseBQQ| forall (u : U32). Type+ u -> Type+ u |]
    Record → [parseBQQ| forall (u : U32). Row (Type+ u) -> Type+ u |]
    Type → [parseBQQ| u : U32 -> Type+ (u + 1) |]
    Eq → [parseBQQ| forall (u : U32) (a : Type+ u). a -> Type+ u |]
    RecordGet →
      [parseBQQ|
        forall (u : U32) (row : Row (Type+ u)) (t : Type+ u).
          tag : Tag ->
          record : Record {(tag : t || row)} ->
          t
      |]

data InferMode a where
  Infer ∷ InferMode TermT
  Check ∷ TermT → InferMode ()

pMode ∷ InferMode a → Doc AnsiStyle
pMode = \case
  Infer → "_"
  Check t → pTerm' t

insertCtx ∷ (Maybe TermT, TermT) → CtxT → CtxT -- TODO: This is absolutely 100% wrong.
insertCtx (xVal, xTy) xs =
  ( if isJust xVal
      then xs
      else (bimap (fmap (nested 1)) (nested 1) <$> xs)
  )
    `revSnoc` (xVal, xTy)

-- Infer value in nested context.
-- inferNested ∷ ∀ sig m a. (Has Solve sig m) ⇒ CtxT → TermT → InferMode a → m a
-- inferNested ctx val Infer = nested (-1) <$> infer ctx val Infer
-- inferNested ctx val (Check ty) = infer ctx val $ Check $ nested 1 ty

-- TODO: beforeEx DOESN'T CONSIDER INTRODUCED VARIABLES, ACTUALLY!

-- | Either infers a normalized type for the value and context, or checks a value against the normalized type.
infer ∷ ∀ sig m a. (Has Solve sig m) ⇒ CtxT → TermT → InferMode a → m a
infer ctx = (\t mode → stackScope ("<" <> pTerm' t <> "> : " <> pMode mode) $ infer' t mode)
 where
  -- Here, we will convert Checks to Infers.
  -- However, converting Infer to a Check when checking a term is hereby declared a deadly sin.
  infer' = curry \case
    (term, Check (Quantification Forall _ xTy yT)) → scoped_ do
      x' ← pushUniVar xTy
      pure do
        yT' ← normalize (NormRewrite (Var 0) x') yT
        infer ctx term $ Check yT'
    -- TODO: breaks.
    -- (term, Check ((Quantification Exists xName Ty yT))) → scoped_ do -- TODO: not just for Ty!
    --   x' ← pushExVar
    --   yT' ← normalize (HM.singleton xName x') yT
    --   infer ctx term $ Check $ yT'
    (Block (BlockLet name tyM val) into, mode) → do
      ty ← stackScope ("let" <+> pIdent name) case tyM of
        Nothing → infer ctx val Infer
        Just ty → do
          -- TODO: check ty' to be a type?
          -- EDIT: typechecking is undecidable... so... uh... no?
          -- void $ infer ctx ty Infer
          ty' ← normalize (NormBinds $ fst <$> ctx) ty
          infer ctx val $ Check ty'
          pure ty'
      val' ← normalize (NormBinds $ fst <$> ctx) val
      let withBs' act = case into of
            Block{} → act into
            _ → stackScope "in" $ act into
      withBs' \bs' →
        infer
          (insertCtx (Just val', ty) ctx)
          bs'
          mode
    (Lam arg bod, Infer) →
      scoped do
        u ← pushExVar $ Just $ Builtin U32
        inT ← pushExVar $ Just $ typOf u
        pure do
          outT ← infer (insertCtx (Nothing, inT) ctx) bod Infer
          traceShowM $ pTerm' $ Pi Nothing inT outT
          pure $ Pi Nothing inT outT
    (Lam arg bod, Check (Pi inNameM inT outT)) → do
      let inferBod val outT' = infer (insertCtx (val, inT) ctx) bod $ Check outT'
      case inNameM of
        Nothing → inferBod Nothing outT
        Just inName → scoped_ do
          arg' ← pushUniVar inT
          pure do
            outT' ← normalize (NormRewrite (Var 0) arg') outT
            inferBod (Just arg') outT'
    -- pure do
    --   outT' ← normalize (NormBinds $ [Just arg']) outT
    --   inferBod (Just arg') outT'
    (Op a _op b, Infer) → do
      -- Deadly sin. Should be fixed.
      infer ctx a $ Check $ Builtin U32
      infer ctx b $ Check $ Builtin U32
      pure $ Builtin U32
    -- Override for second-class RecordGet
    -- TODO: Create a speci type for RecordGet
    (App (App (Builtin RecordGet) tag) record, Infer) → do
      recordTy ← infer ctx record Infer
      let body row = do
            withLookupField
              ( \case
                  LookupFound x _ → do
                    self ← normalize (NormBinds $ fst <$> ctx) record
                    -- TODO: This replaces `self` with the entire record.
                    -- It doesn't filter out only the accessible fields.
                    -- It's quite easy to filter by updating the lookupField, but do we need it really?
                    -- As I understand it, the inference should fail first.
                    x' ← normalize (NormBinds [Just self]) x
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
        ( \var (mScope, mT) → beforeEx mScope var do
            u ← pushExVar $ Just $ Builtin U32
            row ← pushExVar $ Just $ rowOf $ typOf u
            pure do
              writeMeta (mScope, mT) var $ recordOf row
              body row
        )
        \case
          App (Builtin Record) row → body row
          _ → stackError "Not a record"
    {-
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
                    x' ← normalize (HM.singleton (Ident "self") selfLazy') x
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
              u ← pushExVar $ Just $ Builtin U32
              row ← pushExVar $ Just $ rowOf $ typOf u
              pure do
                writeMeta (mScope, mT) var $ recordOf row
                body row
        )
        \case
          App (Builtin Record) row → body row
          _ → stackError "Not a record"
    -}
    (App f a, Infer) → do
      fTy ← infer ctx f Infer
      withMono
        id
        fTy
        ( \var (mScope, mT) →
            -- I'm not satisfied by this solution, but instMeta solution is
            -- even more verbose since it accepts full TermT as input.
            beforeEx mScope var do
              i ← pushExVar $ Just $ Builtin U32
              inT ← pushExVar $ Just $ typOf i
              outT ← pushExVar $ Just $ typOf i
              pure do
                writeMeta (mScope, mT) var (Pi Nothing inT outT)
                infer ctx a $ Check $ inT
                pure outT
        )
        \case
          Pi inNameM inT outT → do
            infer ctx a $ Check $ inT
            case inNameM of
              Nothing → pure outT
              Just _inNameM → do
                a' ← normalize (NormBinds $ fst <$> ctx) a
                normalize
                  (NormBinds [Just a'])
                  outT
          t → stackError $ "inferApp " <> pTerm' t
    (NatLit _, Infer) → pure $ Builtin U32
    (TagLit _, Infer) → pure $ Builtin Tag
    {-
        (FieldsLit FRecord knownVal rest, Infer) → do
          knownTy ← for knownVal \(name, val) → do
            infer ctx name $ Check $ Builtin Tag
            ty ← infer ctx val Infer
            pure (name, ty)
          rest' ← for rest \rest' → do
            restT ← infer ctx rest' Infer
            withMono
              id
              restT
              ( \var (mScope, mT) →
                  beforeEx mScope var do
                    u ← pushExVar $ Just $ Builtin U32
                    row ← pushExVar $ Just $ rowOf $ typOf u
                    pure do
                      writeMeta (mScope, mT) var $ recordOf row
                      pure row
              )
              \case
                App (Builtin Record) row → pure row
                t → stackError $ "inferRecord " <> pTerm 0 t
          pure $ recordOf $ FieldsLit FRow knownTy rest'
        (FieldsLit FRow known rest, Check (App (Builtin Row) ty)) → do
          let extSelf field =
                HM.adjust
                  ( \case
                      (Nothing, App (Builtin Record) (FieldsLit FRow existing r)) →
                        (Nothing, recordOf $ FieldsLit FRow (field : existing) r) -- TODO: RevList? Seq?
                      _ → error "impossible"
                  )
                  (Ident "self")
          ctx' ←
            foldM
              ( \ctx' (name, val) → do
                  infer ctx' name $ Check $ Builtin Tag
                  infer ctx' val $ Check ty
                  name' ← normalize ctx' name
                  val' ← normalize ctx' val
                  pure $ extSelf (name', val') ctx'
              )
              ctx
              known
          for_ rest \rest' → infer ctx' rest' $ Check $ rowOf ty
        (FieldsLit FRow known rest, Infer) → scoped do
          t ← pushExVar Nothing
          pure do
            infer ctx (FieldsLit FRow known rest) $ Check $ rowOf t
            pure $ rowOf t
        (FieldsLit FRecord [] restM, Check (App (Builtin Record) row)) →
          case restM of
            Just rest → infer ctx rest $ Check $ recordOf row
            Nothing → subtype (FieldsLit FRow [] Nothing) row
        (FieldsLit FRecord ((name, val) : fields) rest, Check (App (Builtin Record) row)) → do
          name' ← normalize ctx name
          withLookupField
            ( \case
                LookupFound ty row' → do
                  infer ctx val $ Check $ ty
                  val' ← normalize ctx val
                  row'' ←
                    normalize
                      (HM.insert (Ident "self") (mkFromTerm (Proxy @m) $ FieldsLit FRecord [(name', val')] Nothing) ctx)
                      $ uncurry (FieldsLit FRow) row'
                  infer ctx (FieldsLit FRecord fields rest) $ Check $ recordOf row''
                x → stackError $ "FRecord: " <> pretty (show x)
            )
            (\_ x → x)
            True
            name
            ([], Just row)
        (Sorry _ x, Infer) → normalize (HM.mapMaybe fst ctx) x -- TODO: dedup
    -}
    (Var x, Infer) → case unUnsafeRevList ctx !? x of
      Nothing → stackError $ "Unknown var @" <> pretty x
      Just (_, ty) → pure ty
    {-
        (Quantification _ name kind ty, mode) → scoped_ do
          u ← pushExVar $ Just $ Builtin U32
          pure do
            infer ctx kind $ Check $ typOf u
            kind' ← normalize (HM.mapMaybe fst ctx) kind
            -- TODO: investigate correctness. This allows things like:
            -- `forall x. Type -> x` : Kind
            -- TODO: ... this allows things like:
            -- /: fadeno.U32 -> fadeno.U32
            -- forall (x : fadeno.U32). (\y. x + y)
            -- ... so this is absolutely wrong, need to think about this.
            infer (HM.insert name (Nothing, kind') ctx) ty mode
        (Pi inNameM x y, Check (App (Builtin Type) u)) → do
          infer ctx x $ Check $ typOf u
          infer (maybe id (`HM.insert` (Nothing, x)) inNameM ctx) y $ Check $ typOf u
        (Pi inNameM x y, Infer) → scoped do
          u ← pushExVar $ Just $ Builtin U32
          pure do
            infer ctx (Pi inNameM x y) $ Check $ typOf u
            pure $ typOf u
      -}
    (Builtin x, Infer) → pure $ typOfBuiltin x
    (BuiltinsVar, Infer) → pure $ App (Builtin Record) $ FieldsLit FRow ((\b → (TagLit $ identOfBuiltin b, typOfBuiltin b)) <$> builtinsList) Nothing -- infer ctx builtinsVar Infer -- TODO: redo.
    (ExVar (ExVar' i) nesting, mode) →
      sendIO (readIORef i) >>= \case
        Left t → infer ctx (nested nesting t) mode
        Right (_, Just ty) → case mode of
          Infer → pure $ nested nesting ty
          Check ty2 → subtype (nested nesting ty) ty2
        Right (_, Nothing) → stackError "Cannot infer value of existential metavariable"
    (UniVar _ _ t, Infer) → pure t
    (term, Check c) → stackScope ("check via infer" <+> pTerm' term <+> ":" <+> pTerm' c) do
      ty ← infer ctx term Infer
      subtype ty c

-- | a <: b
subtype ∷ ∀ sig m. (Has Solve sig m) ⇒ TermT → TermT → m ()
subtype = \a b →
  stackScope (pTerm' a <+> annotate (color Cyan) "<:" <+> pTerm' b) do
    a' ← unwrapExs a
    b' ← unwrapExs b
    subtype' (a', b')
 where
  subtype' = \case
    {-
          (aT, (Quantification Forall xName xTy bT)) → scoped_ do
            x' ← pushUniVar xTy
            pure do
              bT' ← normalize (HM.singleton xName x') bT
              subtype (aT) (bT')
          ((Quantification Exists xName xTy aT), bT) → scoped_ do
            x' ← pushUniVar xTy
            pure do
              aT' ← normalize (HM.singleton xName x') aT
              subtype (aT') (bT)
          ((Quantification Forall xName xTy aT), bT) → scoped_ do
            x' ← pushExVar $ Just xTy
            pure do
              aT' ← normalize (HM.singleton xName x') aT
              subtype (aT') (bT)
          (aT, (Quantification Exists xName xTy bT)) → scoped_ do
            x' ← pushExVar $ Just xTy
            pure do
              bT' ← normalize (HM.singleton xName x') bT
              subtype (aT) (bT')
    -}
    ((ExVar a aScope), bT) → subtypeMeta a aScope bT
    (aT, (ExVar b bScope)) → subtypeMeta b bScope aT
    ((UniVar a1 b1 _), (UniVar a2 b2 _))
      | a1 == a2 && b1 == b2 → pure ()
    {-
          ((Pi aNameM a b), (Pi cNameM c d)) → scoped_ do
            subtype (c) (a)
            e ← pushUniVar $ c
            pure do
              b' ← maybe pure (\aName → normalize $ HM.singleton aName e) aNameM b
              d' ← maybe pure (\cName → normalize $ HM.singleton cName e) cNameM d
              subtype (b') (d')
          -- ((App f1 a1), (App f2 a2)) → do
          --   -- TODO: not sure
          --   subtype (f1) (f2)
          --   subtype (f2) (f1)
          --   subtype (a1) (a2)
          --   subtype (a2) (a1)
          ((FieldsLit FRow _ _), (FieldsLit FRow [] Nothing)) → pure ()
          ((FieldsLit FRow [] (Just a)), b) → subtype (a) b -- TODO: What if a is not FieldsLit
          ((FieldsLit FRow fields rest), (FieldsLit FRow ((nameReq, valReq) : fieldsReq) restReq)) → do
            withLookupField
              ( \case
                  LookupFound val (fields', rest') → do
                    subtype val valReq
                    scoped_ do
                      e ← pushUniVar val
                      pure do
                        let mkRest f r = normalize (HM.singleton (Ident "self") $ FieldsLit FRecord [(nameReq, e)] Nothing) $ FieldsLit FRow f r
                        aT ← mkRest fields' rest'
                        bT ← mkRest fieldsReq restReq
                        subtype aT bT
                  _ → stackError "<: lookup unknown todo"
              )
              (\_ x → x)
              True
              nameReq
              (fields, rest)
    -}
    (Builtin a, Builtin b)
      | a == b → pure ()
    (App (Builtin Type) a, App (Builtin Type) b) → do
      a' ← unwrapExs a
      b' ← unwrapExs b
      case (a', b') of
        (NatLit x, NatLit y)
          | x <= y → pure ()
        (ExVar a'' aScope, _) → subtypeMeta a'' aScope b
        (_, ExVar b'' bScope) → subtypeMeta b'' bScope a
        _ → stackError $ "Cannot check that universe" <+> pTerm' a <+> "<=" <+> pTerm' b
  {-
        (App (Builtin Record) aT, App (Builtin Record) bT) → subtype aT bT
        (App (Builtin Row) aT, App (Builtin Row) bT) → subtype aT bT
        -- ((Row aT), (Row bT)) → subtype (aT) (bT)
        -- (U32, U32) → pure ()
        -- (Ty, Ty) → pure ()
        -- (Tag, Tag) → pure ()
        -- ((Record aT), (Record bT)) → subtype (aT) (bT)
        -- ((Row aT), (Row bT)) → subtype (aT) (bT)
        (aT, bT) → stackError $ pTerm 0 aT <+> "<:" <+> pTerm 0 bT
    -}
  unwrapExs ∷ TermT → m TermT
  unwrapExs inp = case inp of
    (Sorry _ t) → unwrapExs $ t
    (ExVar (ExVar' a) scope) →
      sendIO (readIORef a) >>= \case
        Left i → unwrapExs $ nested scope i
        _ → pure inp
    _ → pure inp
  subtypeMeta (ExVar' a) aScope bT =
    sendIO (readIORef a) >>= \case
      Left _ → error "Impossible"
      Right (_, aT) → instMeta (aScope, aT) (ExVar' a) bT

runSolveM ∷ (Applicative m) ⇒ StateC (RevList (RevList ExVar')) (FreshC (ErrorC (Doc AnsiStyle) m)) a → m (Either (Doc AnsiStyle) a)
runSolveM =
  runError (pure . Left) (pure . Right)
    . evalFresh 0
    . evalState mempty

checkFile ∷ FilePath → IO ()
checkFile file = do
  term ← parseFile file
  (stacks, res) ← runStackAccC $ runSolveM $ infer [] term Infer
  render case res of
    Left e →
      pStacks stacks
        <> line
        <> annotate (color Red) "error: "
        <> e
    Right r → pTerm' r

-- TODO: dedup
checkFileDebug ∷ FilePath → IO ()
checkFileDebug file = do
  term ← parseFile file
  res ← runStackPrintC $ runSolveM $ infer [] term Infer
  render case res of
    Left e → annotate (color Red) "error: " <> e
    Right r → pTerm' r

main ∷ IO ()
main = pure ()
