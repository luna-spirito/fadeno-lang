{-# LANGUAGE UndecidableInstances #-}

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
import Normalize (normalize, parseBQQ)
import Parser (ExVar' (..), Ident (..), RevList (..), TermT (..), render)
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
type CtxT = [(Maybe TermT, TermT)] -- Actually stores just Idents, but VarT for easier conversion.

data SEntry = SScope | SExVar

-- | For meta-variables
type Solve = State (IntMap (RevList ExVar')) :+: Fresh :+: Error (Doc AnsiStyle) :+: StackLog :+: Lift IO

freshIdent ∷ (Has Solve sig m) ⇒ m Ident
freshIdent = UIdent <$> fresh

pushExVar ∷ (Has (Writer (RevList ExVar') :+: Reader Int :+: Solve) sig m) ⇒ Maybe TermT → m TermT
pushExVar t = do
  scope ← ask
  name ← freshIdent
  metaVar' ← fmap ExVar' $ sendIO $ newIORef $ Right (name, t)
  tell @(RevList _) [metaVar']
  pure $ ExVar metaVar' scope

pushUniVar ∷ (Has (Reader Int :+: Solve) sig m) ⇒ TermT → m TermT
pushUniVar ty = do
  -- Pushed ephemerally.
  scope ← ask
  ident ← freshIdent
  pure $ UniVar ident scope ty

-- I hate this.
revInsertBefore ∷ ∀ a. RevList a → (a → Bool) → RevList a → RevList a
revInsertBefore ins f = go
 where
  go = \case
    UnsafeRevList [] → error "impossible"
    UnsafeRevList (x : xs)
      | f x → [x] <> ins <> (UnsafeRevList xs)
      | otherwise →
          let (UnsafeRevList xs') = go $ UnsafeRevList xs
           in UnsafeRevList $ x : xs'

-- Probably access to Solve should be restricted in ExVarPushC...
type ExVarPushC m = ReaderC Int (WriterC (RevList ExVar') m)

beforeEx ∷ (Has Solve sig m) ⇒ Int → ExVar' → (ExVarPushC m (m a)) → m a
beforeEx scope ex act = do
  (inserted, resM) ← runWriter (curry pure) $ runReader scope act
  modify $ IM.adjust (revInsertBefore inserted (== ex)) scope
  resM

scoped' ∷ (Has Solve sig m) ⇒ ((TermT → TermT) → a → a) → ExVarPushC m (m a) → m a
scoped' tmap act = do
  (origExs, tyM) ← runWriter (curry pure) $ runReader 0 act
  modify $ IM.insert scope origExs
  ty ← tyM
  UnsafeRevList exs ← state @(IntMap (RevList ExVar')) \scopes →
    (IM.deleteMax scopes, snd $ fromMaybe (error "Internal error: Scope disappeared") $ IM.lookupMax scopes)
  foldM
    ( \ty' (ExVar' x) →
        sendIO (readIORef x) >>= \case
          Left t → stackError $ "Internal error: Resolved existential wasn't marked as such:" <+> pTerm 0 t
          Right (_, (_, xTyM)) → do
            variable ← fresh
            let variable' = Ident $ BS.pack $ "/" <> show variable
            sendIO $ writeIORef x $ Left $ Var variable'
            -- TODO: extract name for new variable from the existential.
            let ofT t = Quantification Forall variable' t `tmap` ty'
            case xTyM of
              Just xTy → pure $ ofT xTy
              Nothing → do
                n ← freshIdent
                pure $ Quantification Forall n (Builtin U32) `tmap` ofT (typOf $ Var n)
    )
    ty
    exs

{-

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
  scope ← IM.size @(RevList ExVar') <$> get
  (origExs, tyM) ← runWriter (curry pure) $ runReader scope act
  modify $ IM.insert scope origExs
  ty ← tyM
  modify $ IM.deleteMax @(RevList ExVar')
  pure ty

{-
scoped ∷ (Has Solve sig m) ⇒ ExVarPushC m (m TermT) → m TermT
scoped = scoped' id

markSolved ∷ (Has Solve sig m) ⇒ Int → ExVar' → m ()
markSolved scope var = do
  modify @(IntMap (RevList ExVar')) \scopes →
    IM.adjust (\(UnsafeRevList l) → UnsafeRevList $ filter (/= var) l) scope scopes

-- Writes & checks
writeMeta ∷ (Has Solve sig m) ⇒ (Int, Maybe TermT) → ExVar' → TermT → m ()
writeMeta (scope, tyM) (ExVar' var) val = do
  for_ tyM $ infer [] val . Check
  -- stackLog $ "?" <> pTerm 0 (ExVar $ ExVar' var) <+> "=" <+> pTerm 0 val
  sendIO $ writeIORef var $ Left val
  markSolved scope (ExVar' var)

-- TODO: So, return the proper ordering, but just use
instMeta ∷ ∀ sig m. (Has Solve sig m) ⇒ (Int, Maybe TermT) → ExVar' → TermT → m ()
instMeta = (\f a b c → stackScope "instMeta" $ f a b c) \(scope1, t1) origVar1 →
  let instMeta' ∷ TermT → m TermT
      instMeta' = \case
        Sorry _ x → instMeta' x
        ExVar (ExVar' var2) →
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
                              | x == ExVar' var2 → False
                              | otherwise → go xs
                            _ → error "Imposible"
                      UnsafeRevList exs ← fromJust . IM.lookup scope1 <$> get
                      pure $ go exs
              if var2Earlier
                then pure $ ExVar $ ExVar' var2
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
        x → stackError $ "instMeta (of" <+> pretty scope1 <> ")" <+> pTerm 0 x
   in \val →
        let r = writeMeta (scope1, t1) origVar1 =<< instMeta' val
         in case val of
              ExVar (ExVar' var2) →
                if origVar1 == ExVar' var2
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
    ExVar (ExVar' var) →
      sendIO (readIORef var) >>= \case
        Left v → withMono' onMeta onOther v
        Right (_, v) → onMeta (ExVar' var) v
    Quantification Forall name kind v → scoped' tmap do
      ty ← pushExVar $ Just kind
      pure $ withMono' onMeta onOther =<< normalize (HM.singleton name ty) v
    Quantification Exists name kind v → scoped' tmap do
      ty ← pushUniVar kind
      pure $ withMono' onMeta onOther =<< normalize (HM.singleton name ty) v
    r → onOther r

-- | Intensional equality.
data EqRes
  = EqYes -- provably eq
  | EqNot -- provably uneq
  | EqUnknown

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
  notARow x = stackError $ "Not a row:" <+> pTerm 0 x
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
              _ → notARow $ ExVar var
            else const $ cont LookupMissing
      )
      \case
        FieldsLit FRow vals rest → rec prev (vals, rest)
        x → stackError $ "lookupField todo " <> pTerm 0 x
    ((name, val) : xs, rest) →
      isEq needle name >>= \case
        EqYes → cont $ LookupFound val (toList prev <> xs, rest)
        EqUnknown → cont LookupUnknown
        EqNot → rec (prev `revSnoc` (name, val)) (xs, rest)

{- | Checks if two normalized terms are intensionally equivalent.
TODO: η-conversion
-}
isEq ∷ (Has Solve sig m) ⇒ TermT → TermT → m EqRes
isEq = curry \case
  (Block{}, _) → undefined
  (Var _, _) → undefined
  (_, Block{}) → undefined
  (_, Var _) → undefined
  (UniVar a _ _, UniVar b _ _)
    | a == b → pure EqYes
  (UniVar{}, _) → pure EqUnknown
  (_, UniVar{}) → pure EqUnknown
  -- TODO: ExVar? I don't know!
  (ExVar{}, _) → stackError "isEq ExVar"
  (_, ExVar{}) → stackError "isEq ExVar"
  (App f1 a1, App f2 a2) → tryEq f1 f2 $ tryEq a1 a2 $ pure EqYes
  (App{}, _) → pure EqUnknown
  (_, App{}) → pure EqUnknown
  (Op a1 op1 b1, Op a2 op2 b2)
    | op1 == op2 → tryEq a1 a2 $ tryEq b1 b2 $ pure EqYes
  (Op{}, _) → pure EqUnknown
  (_, Op{}) → pure EqUnknown
  (Sorry _ a, b) → isEq a b
  (a, Sorry _ b) → isEq a b
  -- (BuiltinsVar, b) → isEq builtinsVa
  -- Literals
  (Lam arg1 bod1, Lam arg2 bod2) → scoped_ do
    arg ← pushUniVar undefined -- "Kind" actually doesn't matter.
    pure do
      bod1' ← normalize (HM.singleton arg1 arg) bod1
      bod2' ← normalize (HM.singleton arg2 arg) bod2
      isEq bod1' bod2'
  (Lam _ _, _) → pure EqNot
  (NatLit a, NatLit b)
    | a == b → pure EqYes
  (NatLit _, _) → pure EqNot
  (TagLit a, TagLit b)
    | a == b → pure EqYes
  (TagLit _, _) → pure EqNot
  -- (FieldsLit FRecord vals1 rest1M, FieldsLit FRecord vals2 rest2M) →
  --   case (vals1, rest1M) of
  --     ([], Nothing) → case (vals2, rest2M) of
  --       ([], Nothing) → pure EqYes
  --       _ → pure EqNot
  --     ([], Just rest1) → isEq rest1 (FieldsLit FRecord vals2 rest2M)
  --     ((name1, val1):xs, rest1) →
  --       lookupField False name1 (vals2, rest2M) >>= \case
  --         LookupFound val2 (vals2', rest2') → isEq val1 val2 >>= \case
  --           EqYes → isEq (FieldsLit FRecord xs rest1) (FieldsLit FRecord vals2' rest2')
  --           EqNot → pure EqNot
  --           EqUnknown → pure EqUnknown
  --         LookupMissing → pure EqNot
  --         LookupUnknown → pure EqUnknown
  -- (FieldsLit FRecord _ _, _) → pure EqNot
  (Quantification q1 n1 k1 t1, Quantification q2 n2 k2 t2)
    | q1 == q2 →
        isEq k1 k2 >>= \case
          EqYes → scoped_ do
            arg ← pushUniVar undefined
            pure do
              t1' ← normalize (HM.singleton n1 arg) t1
              t2' ← normalize (HM.singleton n2 arg) t2
              isEq t1' t2'
          x → pure x
  (Quantification{}, _) → pure EqNot
  (Builtin a, Builtin b)
    | a == b → pure EqYes
  (Builtin _, _) → pure EqNot
  (_, Builtin _) → pure EqNot
  (BuiltinsVar, BuiltinsVar) → pure EqYes
  (BuiltinsVar, _) → pure EqNot
  (_, BuiltinsVar) → pure EqNot
  -- (U32, U32) → pure EqYes
  -- (U32, _) → pure EqNot
  -- (Tag, Tag) → pure EqYes
  -- (Tag, _) → pure EqNot
  -- (Row a, Row b) → isEq a b
  -- (Row _, _) → pure EqNot
  -- TODO: override self as soon as you start type-checking row!
  -- (Record x, Record y) → isEq x y
  -- (Record _, _) → pure EqNot
  (Pi inNameM1 inT1 outT1, Pi inNameM2 inT2 outT2) →
    isEq inT1 inT2 >>= \case
      EqYes → scoped_ do
        arg ← pushUniVar undefined
        pure do
          outT1' ← maybe pure (\name → normalize $ HM.singleton name arg) inNameM1 outT1
          outT2' ← maybe pure (\name → normalize $ HM.singleton name arg) inNameM2 outT2
          isEq outT1' outT2'
      x → pure x
  (Pi{}, _) → pure EqNot
  -- (Ty, Ty) → pure EqYes
  -- (Ty, _) → pure EqNot
  (FieldsLit _ _ _, _) → stackError "isEq Fields todo"
 where
  -- (Access _ _, _) -> stackError "isEq Access todo" -- Equate all fields that are Unknown eq to tag.

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

infer ∷ ∀ sig m a. (Has Solve sig m) ⇒ CtxT → TermT → InferMode a → m a
infer ctx = (\t mode → stackScope (pTerm 0 t) $ infer' t mode)
 where
  -- Here, we will convert Checks to Infers.
  -- However, converting Infer to a Check when checking a term is hereby declared a deadly sin.
  infer' = curry \case
    (term, Check (Quantification Forall xName xTy yT)) → scoped_ do
      x' ← pushUniVar xTy
      pure do
        yT' ← normalize (HM.singleton xName x') yT
        infer ctx term $ Check $ yT'
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
          ty' ← normalize ctx ty
          infer ctx val $ Check ty'
          pure ty'
      val' ← normalize ctx val
      let withBs' act = case into of
            Block{} → stackScope "in" $ act into
            _ → act into
      withBs' \bs' →
        infer
          (HM.insert name (Just val', ty) ctx)
          bs'
          mode
    -- (Block (BlockRewrite with) into, mode) → _
    (Lam arg bod, Infer) →
      scoped do
        u ← pushExVar $ Just $ Builtin U32
        inT ← pushExVar $ Just $ typOf u
        pure do
          outT ← infer (HM.insert arg (Nothing, inT) ctx) bod Infer
          pure $ Pi Nothing inT outT
    (Lam arg bod, Check (Pi inNameM inT outT)) → do
      inT' ← normalize (HM.mapMaybe fst ctx) inT
      let inferBod val outT' = infer (HM.insert arg (val, inT') ctx) bod $ Check outT'
      case inNameM of
        Nothing → inferBod Nothing outT
        Just inName → scoped_ do
          arg' ← pushUniVar inT'
          pure do
            outT' ← normalize (HM.singleton inName arg') outT
            inferBod (Just arg') outT'
    (Op a _op b, Infer) → do
      -- Deadly sin. Should be fixed.
      infer ctx a $ Check $ Builtin U32
      infer ctx b $ Check $ Builtin U32
      pure $ Builtin U32
    -- Override for second-class RecordGet
    (App (App (Builtin RecordGet) tag) record, Infer) → do
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
              Just inName → do
                a' ←
                  normalize
                    (HM.mapMaybe fst ctx)
                    a
                normalize
                  (HM.singleton inName a')
                  outT
          t → stackError $ "inferApp " <> pTerm 0 t
    (NatLit _, Infer) → pure $ Builtin U32
    (TagLit _, Infer) → pure $ Builtin Tag
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
    (Var x, Infer) → case HM.lookup x ctx of
      Nothing → stackError $ "Unknown var " <> pIdent x
      Just (_, ty) → pure ty
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
    (Builtin x, Infer) → pure $ typOfBuiltin x
    (BuiltinsVar, Infer) → pure $ App (Builtin Record) $ FieldsLit FRow ((\b → (TagLit $ identOfBuiltin b, typOfBuiltin b)) <$> builtinsList) Nothing -- infer ctx builtinsVar Infer -- TODO: redo.
    (ExVar (ExVar' i), mode) →
      sendIO (readIORef i) >>= \case
        Left t → infer ctx t mode
        Right (_, (_, Just ty)) → case mode of
          Infer → pure ty
          Check ty2 → subtype ty ty2
        Right (_, (_, Nothing)) → stackError "Cannot infer value of existential metavariable"
    (UniVar _ _ t, Infer) → pure t
    (term, Check c) → stackScope ("check via infer" <+> pTerm 0 term <+> ":" <+> pTerm 0 c) do
      ty ← infer ctx term Infer
      subtype ty c

-- | a <: b
subtype ∷ ∀ sig m. (Has Solve sig m) ⇒ TermT → TermT → m ()
subtype = \a b →
  stackScope (pTerm 0 a <+> annotate (color Cyan) "<:" <+> pTerm 0 b) do
    a' ← unwrapExs a
    b' ← unwrapExs b
    subtype' (a', b')
 where
  subtype' = \case
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
    ((ExVar a), bT) → subtypeMeta a bT
    (aT, (ExVar b)) → subtypeMeta b aT
    ((UniVar a _ _), (UniVar b _ _))
      | a == b → pure ()
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
    (Builtin a, Builtin b)
      | a == b → pure ()
    (App (Builtin Type) a, App (Builtin Type) b) → do
      a' ← unwrapExs a
      b' ← unwrapExs b
      case (a', b') of
        (NatLit x, NatLit y)
          | x <= y → pure ()
        (ExVar a'', _) → subtypeMeta a'' b
        (_, ExVar b'') → subtypeMeta b'' a
        _ → stackError $ "Cannot check that universe" <+> pTerm 0 a <+> "<=" <+> pTerm 0 b
    (App (Builtin Record) aT, App (Builtin Record) bT) → subtype aT bT
    (App (Builtin Row) aT, App (Builtin Row) bT) → subtype aT bT
    -- ((Row aT), (Row bT)) → subtype (aT) (bT)
    -- (U32, U32) → pure ()
    -- (Ty, Ty) → pure ()
    -- (Tag, Tag) → pure ()
    -- ((Record aT), (Record bT)) → subtype (aT) (bT)
    -- ((Row aT), (Row bT)) → subtype (aT) (bT)
    (aT, bT) → stackError $ pTerm 0 aT <+> "<:" <+> pTerm 0 bT
  unwrapExs ∷ TermT → m TermT
  unwrapExs inp = case inp of
    (Sorry _ t) → unwrapExs $ t
    (ExVar (ExVar' a)) →
      sendIO (readIORef a) >>= \case
        Left i → unwrapExs $ i
        _ → pure inp
    _ → pure inp
  subtypeMeta (ExVar' a) bT =
    sendIO (readIORef a) >>= \case
      Left _ → error "Impossible"
      Right (_, scope) → instMeta scope (ExVar' a) bT

runSolveM ∷ (Applicative m) ⇒ StateC (IntMap (RevList ExVar')) (FreshC (ErrorC (Doc AnsiStyle) m)) a → m (Either (Doc AnsiStyle) a)
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
    Right r → pTerm 0 r

-- TODO: dedup
checkFileDebug ∷ FilePath → IO ()
checkFileDebug file = do
  term ← parseFile file
  res ← runStackPrintC $ runSolveM $ infer [] term Infer
  render case res of
    Left e → annotate (color Red) "error: " <> e
    Right r → pTerm 0 r
-}
-}

main ∷ IO ()
main = pure ()
