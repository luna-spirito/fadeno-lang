{-# LANGUAGE UndecidableInstances #-}

module Main where

import Control.Algebra
import Control.Carrier.Error.Church (ErrorC, runError)
import Control.Carrier.Fresh.Church (FreshC, evalFresh)
import Control.Carrier.Reader (ReaderC, runReader)
import Control.Carrier.State.Church (StateC, evalState)
import Control.Carrier.Writer.Church (WriterC, runWriter)
import Control.Effect.Error (Error, Throw, throwError)
import Control.Effect.Fresh (Fresh, fresh)
import Control.Effect.Lift (Lift, sendIO)
import Control.Effect.Reader (Reader, ask, local)
import Control.Effect.State (State, get, modify, state)
import Control.Effect.Writer (Writer, censor, listen, tell)
import Data.ByteString.Char8 qualified as BS
import Data.Foldable (foldrM)
import Data.RRBVector (Vector, adjust', deleteAt, findIndexL, splitAt, viewr, (!?), (|>))
import GHC.Exts (IsList (..))
import Normalize (EqRes (..), NormCtx (..), isEq, nested, normalize, normalizeFile, parseBQQ, rewrite)
import Parser (BlockT (..), BuiltinT (..), Fields (..), Ident (..), Lambda (..), Quantifier (..), TermT (..), builtinsList, identOfBuiltin, pIdent, pTerm', parseFile, recordOf, render, rowOf, typOf)
import Prettyprinter (Doc, annotate, indent, line, nest, pretty, (<+>))
import Prettyprinter.Render.Terminal (AnsiStyle, Color (..), color)
import RIO hiding (Reader, Vector, ask, filter, link, local, runReader, toList)
import RIO.Partial qualified as P

-- TODO: Refactor unwraps?
-- TODO: portM/unportM?

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
newtype StackAccC m a = StackAccC {unStackAccC ∷ WriterC (Vector StackEntry) m a}
  deriving (Functor, Applicative, Monad)

data StackEntry = StackEntry !(Doc AnsiStyle) ![StackEntry]

instance (Algebra sig m) ⇒ Algebra (StackLog :+: sig) (StackAccC m) where
  alg hdl sig ctx = StackAccC $ case sig of
    L (StackLog x) → do
      tell @(Vector StackEntry) [StackEntry x []]
      pure ctx
    L (StackScope name act) → do
      censor (\entries → [StackEntry name $ toList @(Vector _) entries])
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
runStackAccC = runWriter (\w a → pure (toList @(Vector _) w, a)) . unStackAccC

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

-- type Solve = Reader BindsT :+: State MetaVarsT :+: Fresh :+: Error (Doc AnsiStyle) :+: StackLog :+: Lift IO
-- Reader Binds could be included, but probably unnecessary.
type Solve = Writer (IntMap TermT) :+: Fresh :+: Error (Doc AnsiStyle) :+: StackLog

data InferMode a where
  Infer ∷ InferMode TermT
  Check ∷ TermT → InferMode ()

pMode ∷ InferMode a → Doc AnsiStyle
pMode = \case
  Infer → "_"
  Check t → pTerm' t

-- insertCtx ∷ (Maybe TermT, TermT) → BindsT → BindsT -- TODO: This is absolutely 100% wrong.
-- insertCtx (xVal, xTy) xs =
--   ( if isJust xVal
--       then xs
--       else (bimap (fmap (nestedVal 1)) (nestedVal 1) <$> xs)
--   )
--     `revSnoc` (xVal, xTy)

-- Infer value in nested context.
-- inferNested ∷ ∀ sig m a. (Has Solve sig m) ⇒ BindsT → TermT → InferMode a → m a
-- inferNested ctx val Infer = nested (-1) <$> infer ctx val Infer
-- inferNested ctx val (Check ty) = infer ctx val $ Check $ nested 1 ty

-- TODO: beforeEx DOESN'T CONSIDER INTRODUCED VARIABLES, ACTUALLY!

nestMode ∷ InferMode a → InferMode a
nestMode = \case
  Infer → Infer
  Check x → Check $ nested x

mapTermFor ∷ (Applicative f) ⇒ InferMode a → ((TermT → f TermT) → a → f a)
mapTermFor = \case
  Infer → id
  Check _ → const pure

scopedUniVar ∷ (Has Solve sig m) ⇒ ((TermT → m TermT) → a → m a) → Int → m a → m a
scopedUniVar mapTerm uni1 act = do
  (resolved, res) ← listen @(IntMap TermT) act
  let
    ensureNotOcc =
      rewrite
        (const id)
        id
        ( \term () → case term of
            UniVar _ uni2 _ | uni1 == uni2 → Just $ stackError "UniVar leaked"
            _ → Nothing
        )
        ()
  for_ resolved ensureNotOcc
  mapTerm ensureNotOcc res

scopedVar ∷ (Has Solve sig m) ⇒ ((TermT → m TermT) → a → m a) → m a → m a
scopedVar mapTerm act = do
  (resolved, res) ← intercept @(IntMap TermT) act
  let
    unnest =
      rewrite
        (const (+ 1))
        (+ 1)
        ( \term locs → case term of
            Var i | i == locs → Just $ stackError "Var leaked"
            Var i | i > locs → Just $ pure $ Var $ i - 1
            _ → Nothing
        )
        0
  tell =<< for resolved unnest
  mapTerm unnest res

insertBinds ∷ (Maybe TermT, TermT) → Vector (Maybe TermT, TermT) → Vector (Maybe TermT, TermT)
insertBinds new old = (bimap (nested <$>) nested <$> old) |> new

-- | Either infers a normalized type for the value and context, or checks a value against the normalized type.
infer ∷ ∀ sig m a. (Has Solve sig m) ⇒ Vector (Maybe TermT, TermT) → TermT → InferMode a → m a
infer binds = \t mode → stackScope ("<" <> pTerm' t <> "> : " <> pMode mode) $ infer' t mode
 where
  -- Here, we will convert Checks to Infers.
  -- However, converting Infer to a Check when checking a term is hereby declared a deadly sin.
  infer' ∷ TermT → InferMode a → m a
  infer' = curry \case
    (term, Check (Quantification Forall n xTy yT)) → do
      uniId ← fresh
      scopedUniVar (const pure) uniId $ infer binds term $ Check $ normalize [Just $ UniVar n uniId xTy] $ unLambda yT
    -- (term, Check (Quantification Forall _ xTy yT)) → scoped_ do
    --   x' ← pushUniVar $ PortableTerm tyNesting0 xTy
    --   pure do
    --     ctx ← ask @BindsT
    --     yT' ← normalize (nestedNormBinds tyNesting0 [Just $ PortableTerm tyNesting0 x']) yT
    --     infer term $ Check yT'
    -- TODO: breaks.
    -- (term, Check ((Quantification Exists xName Ty yT))) → scoped_ do -- TODO: not just for Ty!
    --   x' ← pushExVar
    --   yT' ← normalize (HM.singleton xName x') yT
    --   infer ctx term $ Check $ yT'
    (Block (BlockLet name tyM val into), mode) → do
      ty ← stackScope ("let" <+> pIdent name) case tyM of
        Nothing → infer binds val Infer
        Just ty → do
          -- TODO: check ty' to be a type?
          -- EDIT: typechecking is undecidable... so... uh... no?
          let ty' = normalize (fst <$> binds) ty
          infer binds val $ Check ty'
          pure ty'
      let
        val' = normalize (fst <$> binds) val
        withLog act = case (unLambda into) of
          Block{} → act
          _ → stackScope "in" act
      withLog
        $ scopedVar (mapTermFor mode)
        $ infer (insertBinds (Just val', ty) binds) (unLambda into)
        $ nestMode mode
    --   (Block (BlockLet name tyM val) into, mode) → do
    --     ctx ← ask @BindsT
    --     ty ← stackScope ("let" <+> pIdent name) case tyM of
    --       Nothing → infer val Infer
    --       Just ty → do
    --         -- TODO: check ty' to be a type?
    --         -- EDIT: typechecking is undecidable... so... uh... no?
    --         -- void $ infer ctx ty Infer
    --         ty' ← normalize (NormBinds 0 $ fst <$> ctx) ty
    --         infer val $ Check ty'
    --         pure ty'
    --     val' ← normalize (NormBinds valNesting0 $ fst <$> ctx) val
    --     let withBs' act = case into of
    --           Block{} → act into
    --           _ → stackScope "in" $ act into
    --     withBs' \bs' →
    --       local (|> (Just $ PortableTerm valNesting0 val', PortableTerm tyNesting0 ty))
    --         $ infer bs' mode
    (Lam arg bod, Infer) → _
    _ → _

--   (Lam arg bod, Infer) →
--     scoped do
--       u ← pushExVar $ Just $ PortableTerm tyNesting0 $ Builtin U32
--       inT ← pushExVar $ Just $ PortableTerm tyNesting0 $ typOf u
--       pure do
--         outT ← local @BindsT (|> (Nothing, PortableTerm tyNesting0 inT)) $ infer bod Infer
--         pure $ Pi Nothing inT outT
--   (Lam arg bod, Check (Pi inNameM inT outT)) → do
--     let inferBod val outT' = local (|> (PortableTerm valNesting0 <$> val, PortableTerm tyNesting0 inT)) $ infer bod $ Check outT'
--     case inNameM of
--       Nothing → inferBod Nothing outT
--       Just inName → scoped_ do
--         arg' ← pushUniVar $ PortableTerm tyNesting0 inT
--         pure do
--           outT' ← normalize (nestedNormBinds tyNesting0 [Just $ PortableTerm tyNesting0 arg']) outT
--           inferBod (Just arg') outT'
--   (Op a _op b, Infer) → do
--     -- Deadly sin. Should be fixed.
--     infer a $ Check $ Builtin U32
--     infer b $ Check $ Builtin U32
--     pure $ Builtin U32
--   -- Override for second-class RecordGet
--   -- TODO: Create a speci type for RecordGet
--   (App (App (Builtin RecordGet) tag) record, Infer) → do
--     recordTy ← infer record Infer
--     let body row = do
--           traceShowM $ pTerm' row
--           withLookupField
--             ( \case
--                 LookupFound x _ → do
--                   ctx ← ask @BindsT
--                   valNesting ← currValNesting -- = valNesting0?
--                   self ← normalize (NormBinds valNesting $ fst <$> ctx) record
--                   -- TODO: This replaces `self` with the entire record.
--                   -- It doesn't filter out only the accessible fields.
--                   -- It's quite easy to filter by updating the lookupField, but do we need it really?
--                   -- As I understand it, the inference should fail first.
--                   traceShowM x
--                   tyNesting ← currTyNesting
--                   x' ← normalize (nestedNormBinds tyNesting [Just $ PortableTerm tyNesting self]) x
--                   traceShowM x'
--                   pure x'
--                 _ → stackError "Field not found"
--             )
--             id
--             True
--             tag
--             ([], Just row)
--     withMono
--       id
--       recordTy
--       ( \var (mScope, mT) → beforeEx mScope var do
--           tyNesting ← currTyNesting
--           u ← pushExVar $ Just $ PortableTerm tyNesting $ Builtin U32
--           row ← pushExVar $ Just $ PortableTerm tyNesting $ rowOf $ typOf u
--           pure do
--             writeMeta (mScope, mT) var $ recordOf row
--             body row
--       )
--       \case
--         App (Builtin Record) row → body row
--         _ → stackError "Not a record"
-- {-
--   recordTy ← infer ctx record Infer
--   let body row =
--         withLookupField
--           ( \case
--               LookupFound x _ → do
--                 selfLazy' ← fmap LazyTerm $ sendIO $ newIORef $ normalize @_ @m ctx record
--                 -- TODO: This replaces `self` with the entire record.
--                 -- It doesn't filter out only the accessible fields.
--                 -- It's quite easy to filter by updating the lookupField, but do we need it really?
--                 -- As I understand it, the inference should fail first.
--                 x' ← normalize (HM.singleton (Ident "self") selfLazy') x
--                 pure x'
--               _ → stackError "Field not found"
--           )
--           id
--           True
--           tag
--           ([], Just row)
--   withMono
--     id
--     recordTy
--     ( \var → \case
--         (mScope, mT) → beforeEx mScope var do
--           u ← pushExVar $ Just $ Builtin U32
--           row ← pushExVar $ Just $ rowOf $ typOf u
--           pure do
--             writeMeta (mScope, mT) var $ recordOf row
--             body row
--     )
--     \case
--       App (Builtin Record) row → body row
--       _ → stackError "Not a record"
-- -}
-- (App f a, Infer) → do
--   fTy ← infer f Infer
--   withMono
--     id
--     fTy
--     ( \var (mScope, mT) →
--         -- I'm not satisfied by this solution, but instMeta solution is
--         -- even more verbose since it accepts full TermT as input.
--         beforeEx mScope var do
--           tyNesting ← currTyNesting
--           i ← pushExVar $ Just $ PortableTerm tyNesting $ Builtin U32
--           inT ← pushExVar $ Just $ PortableTerm tyNesting $ typOf i
--           outT ← pushExVar $ Just $ PortableTerm tyNesting $ typOf i
--           pure do
--             writeMeta (mScope, mT) var (Pi Nothing inT outT)
--             infer a $ Check $ inT
--             pure outT
--     )
--     \case
--       Pi inNameM inT outT → do
--         infer a $ Check $ inT
--         case inNameM of
--           Nothing → pure outT
--           Just _inNameM → do
--             tyNesting ← currTyNesting
--             -- a' ← normalize (NormBinds $ fst <$> ctx) a
--             normalize
--               (nestedNormBinds tyNesting [Just $ PortableTerm tyNesting a])
--               outT
--       t → stackError $ "inferApp " <> pTerm' t
-- (NatLit _, Infer) → pure $ Builtin U32
-- (TagLit _, Infer) → pure $ Builtin Tag
-- {-
--     (FieldsLit FRecord knownVal rest, Infer) → do
--       knownTy ← for knownVal \(name, val) → do
--         infer ctx name $ Check $ Builtin Tag
--         ty ← infer ctx val Infer
--         pure (name, ty)
--       rest' ← for rest \rest' → do
--         restT ← infer ctx rest' Infer
--         withMono
--           id
--           restT
--           ( \var (mScope, mT) →
--               beforeEx mScope var do
--                 u ← pushExVar $ Just $ Builtin U32
--                 row ← pushExVar $ Just $ rowOf $ typOf u
--                 pure do
--                   writeMeta (mScope, mT) var $ recordOf row
--                   pure row
--           )
--           \case
--             App (Builtin Record) row → pure row
--             t → stackError $ "inferRecord " <> pTerm 0 t
--       pure $ recordOf $ FieldsLit FRow knownTy rest'
--     (FieldsLit FRow known rest, Check (App (Builtin Row) ty)) → do
--       let extSelf field =
--             HM.adjust
--               ( \case
--                   (Nothing, App (Builtin Record) (FieldsLit FRow existing r)) →
--                     (Nothing, recordOf $ FieldsLit FRow (field : existing) r) -- TODO: Vector? Seq?
--                   _ → error "impossible"
--               )
--               (Ident "self")
--       ctx' ←
--         foldM
--           ( \ctx' (name, val) → do
--               infer ctx' name $ Check $ Builtin Tag
--               infer ctx' val $ Check ty
--               name' ← normalize ctx' name
--               val' ← normalize ctx' val
--               pure $ extSelf (name', val') ctx'
--           )
--           ctx
--           known
--       for_ rest \rest' → infer ctx' rest' $ Check $ rowOf ty
--     (FieldsLit FRow known rest, Infer) → scoped do
--       t ← pushExVar Nothing
--       pure do
--         infer ctx (FieldsLit FRow known rest) $ Check $ rowOf t
--         pure $ rowOf t
--     (FieldsLit FRecord [] restM, Check (App (Builtin Record) row)) →
--       case restM of
--         Just rest → infer ctx rest $ Check $ recordOf row
--         Nothing → subtype (FieldsLit FRow [] Nothing) row
--     (FieldsLit FRecord ((name, val) : fields) rest, Check (App (Builtin Record) row)) → do
--       name' ← normalize ctx name
--       withLookupField
--         ( \case
--             LookupFound ty row' → do
--               infer ctx val $ Check $ ty
--               val' ← normalize ctx val
--               row'' ←
--                 normalize
--                   (HM.insert (Ident "self") (mkFromTerm (Proxy @m) $ FieldsLit FRecord [(name', val')] Nothing) ctx)
--                   $ uncurry (FieldsLit FRow) row'
--               infer ctx (FieldsLit FRecord fields rest) $ Check $ recordOf row''
--             x → stackError $ "FRecord: " <> pretty (show x)
--         )
--         (\_ x → x)
--         True
--         name
--         ([], Just row)
--     (Sorry _ x, Infer) → normalize (HM.mapMaybe fst ctx) x -- TODO: dedup
-- -}
-- (Var x, Infer) → do
--   ctx ← ask @BindsT
--   case ctx !? x of
--     Nothing → stackError $ "Unknown var @" <> pretty x
--     Just (_, ty) → pure $ unport ty tyNesting0
-- -- {-
-- --     (Quantification _ name kind ty, mode) → scoped_ do
-- --       u ← pushExVar $ Just $ Builtin U32
-- --       pure do
-- --         infer ctx kind $ Check $ typOf u
-- --         kind' ← normalize (HM.mapMaybe fst ctx) kind
-- --         -- TODO: investigate correctness. This allows things like:
-- --         -- `forall x. Type -> x` : Kind
-- --         -- TODO: ... this allows things like:
-- --         -- /: fadeno.U32 -> fadeno.U32
-- --         -- forall (x : fadeno.U32). (\y. x + y)
-- --         -- ... so this is absolutely wrong, need to think about this.
-- --         infer (HM.insert name (Nothing, kind') ctx) ty mode -}
-- (Pi inNameM x y, Check (App (Builtin Type) u)) → do
--   infer x $ Check $ typOf u
--   (if isJust inNameM then local @BindsT (|> (Nothing, PortableTerm valNesting0 x)) else id)
--     $ infer y
--     $ Check
--     $ typOf u
-- (Pi inNameM x y, Infer) → scoped do
--   u ← pushExVar $ Just $ PortableTerm tyNesting0 $ Builtin U32
--   pure do
--     infer (Pi inNameM x y) $ Check $ typOf u
--     pure $ typOf u
-- (Builtin x, Infer) → pure $ unport (typOfBuiltin x) tyNesting0
-- (BuiltinsVar, Infer) →
--   pure
--     $ App (Builtin Record)
--     $ FieldsLit FRow ((\b → (TagLit $ identOfBuiltin b, unport (typOfBuiltin b) (tyNesting0 + 1))) <$> builtinsList) Nothing
-- (ExVar (ExVar' i), mode) →
--   sendIO (readIORef i) >>= \case
--     Left t → infer (unport t nesting) mode
--     Right (_, _, Just ty) → case mode of
--       Infer → pure $ unport ty nesting
--       Check ty2 → subtype (unport ty nesting) ty2
--     Right (_, _, Nothing) → stackError "Cannot infer value of existential metavariable"
-- -- (UniVar _ _ t, Infer) → pure t
-- (k, Infer) → error $ show k
-- (term, Check c) → stackScope ("check via infer" <+> pTerm' term <+> ":" <+> pTerm' c) do
--   ty ← infer term Infer
--   subtype ty c

-- type Solve = Reader BindsT :+: State MetaVarsT :+: Fresh :+: Error (Doc AnsiStyle) :+: StackLog :+: Lift IO

{-
-- data LazyTermT m = LazyTerm !(IORef (m TermT)) | LazyPure !TermT

-- instance (Has Solve sig m) ⇒ HasTerm m (LazyTermT m) where
--   extractTerm (LazyTerm var) = do
--     val ← join $ sendIO $ readIORef var
--     sendIO $ writeIORef var $ pure val
--     pure $ Just val
--   extractTerm (LazyPure x) = pure $ Just x
--   mkFromTerm _ = LazyPure

{- | Context stores values and the type of introduced bindings.
type BindsT = Vector (Maybe TermT, TermT) -- Actually stores just Idents, but VarT for easier conversion.
-}

-- | For meta-variables
type BindsT = Vector (Maybe PortableTermT, PortableTermT)

type MetaVarsT = Vector (Vector ExVar')
type Solve = Reader BindsT :+: State MetaVarsT :+: Fresh :+: Error (Doc AnsiStyle) :+: StackLog :+: Lift IO

currValNesting ∷ (Has (Reader BindsT) sig m) ⇒ m Int
currValNesting = length <$> ask @BindsT
{-# INLINE currValNesting #-}

currTyNesting ∷ (Has (Reader BindsT) sig m) ⇒ m Int
currTyNesting = foldl' (\acc (x, _) → if isNothing x then acc + 1 else acc) 0 <$> ask @BindsT
{-# INLINE currTyNesting #-}

freshIdent ∷ (Has Solve sig m) ⇒ m Ident
freshIdent = UIdent <$> fresh

-- Probably access to Solve should be restricted in ExVarPushC...
type ExVarPushC m = ReaderC Int (WriterC (Vector ExVar') m)

-- `Maybe TermT` is absolute.
pushExVar ∷ (Has (Writer (Vector ExVar') :+: Reader Int :+: Solve) sig m) ⇒ Maybe PortableTermT → m TermT
pushExVar t = do
  scope ← ask
  name ← freshIdent
  metaVar' ← fmap ExVar' $ sendIO $ newIORef $ Right (name, scope, t)
  tell @(Vector _) [metaVar']
  let res = ExVar metaVar'
  stackLog $ "intro" <+> pTerm' res
  pure res

pPortableTerm ∷ PortableTermT → Doc AnsiStyle
pPortableTerm ty = pTerm' $ unport ty 100

pushUniVar ∷ (Has (Reader Int :+: Solve) sig m) ⇒ PortableTermT → m TermT
pushUniVar ty = do
  stackLog $ pPortableTerm ty
  -- Pushed ephemerally.
  scope ← ask
  ident ← freshIdent
  let res = UniVar ident scope ty
  stackLog $ "intro" <+> pTerm' res
  pure res

beforeEx ∷ (Has Solve sig m) ⇒ Int → ExVar' → (ExVarPushC m (m a)) → m a
beforeEx scope ex act = do
  resM ← stackScope ("before " <> pTerm' (ExVar ex)) do
    (inserted, resM) ← runWriter (curry pure) $ runReader scope act
    stackLog . pretty . show =<< get @MetaVarsT
    modify
      $ adjust'
        scope
        ( \exvars →
            let (before, after) = splitAt (P.fromJust $ findIndexL (== ex) exvars) exvars
             in before <> inserted <> after
        )
    pure resM
  resM

scoped' ∷ (Has Solve sig m) ⇒ ((TermT → m TermT) → a → m a) → ExVarPushC m (m a) → m a
scoped' tmap act = do
  scope ← length <$> get @MetaVarsT
  tyM ← stackScope "scoped" do
    (origExs, tyM) ← runWriter (curry pure) $ runReader scope act
    modify (|> origExs)
    pure tyM
  ty ← tyM
  exs ←
    state @MetaVarsT
      $ fromMaybe (error "Internal error: scope disappeared")
      . viewr
  foldrM
    ( \(ExVar' x) ty' →
        sendIO (readIORef x) >>= \case
          Left t → stackError $ "Internal error: Resolved existential wasn't marked as such:" <+> pPortableTerm t
          Right (_, _, xTyM) → do
            variable ← fresh
            let variable' = Ident $ BS.pack $ "/" <> show variable
            -- [0] -> forall. $0
            -- \$0 + [0] -> forall. $1 + $0
            -- \$1 $0 (\ $0 + [1]) -> forall. $2 $1 (\ $0 + $1)
            tyNesting ← currTyNesting
            (`tmap` ty') \resTy → do
              -- A crutch that hopefully doesn't fall off instantly.
              -- TODO: Explain, formalize and hopefully remove the crutch by providing a proper portTerm.
              resTy' ← normalize (nestedNormBinds tyNesting []) resTy
              case xTyM of
                Just xTy → do
                  sendIO $ writeIORef x $ Left $ PortableTerm (tyNesting + 1) $ Var tyNesting
                  pure $ Quantification Forall variable' (unport xTy tyNesting) $ portTerm tyNesting (tyNesting + 1) resTy'
                Nothing → do
                  sendIO $ writeIORef x $ Left $ PortableTerm (tyNesting + 2) $ Var $ tyNesting + 1
                  n ← freshIdent
                  pure
                    $ Quantification Forall n (Builtin U32)
                    $ Quantification Forall variable' (typOf $ Var tyNesting)
                    $ portTerm tyNesting (tyNesting + 2) resTy
    )
    ty
    exs

-- Assumes that all existentias are resolved if they are ever used.
scoped_ ∷ (Has Solve sig m) ⇒ ExVarPushC m (m a) → m a
scoped_ act = do
  -- Bad copy-pasta
  scope ← length <$> get @MetaVarsT
  (origExs, tyM) ← runWriter (curry pure) $ runReader scope act
  modify $ (|> origExs)
  ty ← tyM
  modify $ fst . fromMaybe (error "Internal error: scope disappeared") . viewr @(Vector ExVar')
  pure ty

markSolved ∷ (Has Solve sig m) ⇒ Int → ExVar' → m ()
markSolved scope var =
  modify @MetaVarsT $ adjust' scope \x → deleteAt (fromMaybe (error "impossible") $ findIndexL (== var) x) x

-- Writes & checks
-- TODO: Check that the value is actually writeable and causes no overflows.
writeMeta ∷ (Has Solve sig m) ⇒ (Int, Maybe PortableTermT) → ExVar' → TermT → m ()
writeMeta (scope, tyM) (ExVar' var) val = do
  stackLog $ "refine " <> pTerm' (ExVar (ExVar' var)) <+> "=" <+> pTerm' val
  nesting ← length <$> ask @BindsT
  for_ tyM $ infer val . Check . (`unport` nesting)
  sendIO $ writeIORef var $ Left $ PortableTerm nesting val
  markSolved scope (ExVar' var)

-- TODO: So, return the proper ordering, but just use
-- TODO: Decipher what previous TODO is supposed to mean
-- Instantiates meta with *absolute* value.
instMeta ∷ ∀ sig m. (Has Solve sig m) ⇒ (Int, Maybe PortableTermT) → ExVar' → TermT → m ()
instMeta = (\f a b c → stackScope "instMeta" $ f a b c) \(scope1, t1) origVar1 →
  -- TODO: avoid nested?
  -- Accepts and returns absolute
  let instMeta' ∷ TermT → m TermT
      instMeta' = \case
        Sorry _ x → instMeta' x
        ExVar (ExVar' var2) →
          sendIO (readIORef var2) >>= \case
            Left t → do
              nesting ← currValNesting
              instMeta' $ unport t nesting
            Right (_, scope2, t2) → do
              -- Either var1 or origVar2 is introduced earlier. We need to identify, which one.
              var2Earlier ←
                if
                  | scope2 < scope1 → pure True
                  | scope2 > scope1 → pure False
                  | otherwise → do
                      exs ← fromMaybe (error "Internal error: unknown scope") . (!? scope1) <$> get
                      pure $ findIndexL (== ExVar' var2) exs < findIndexL (== origVar1) exs
              if var2Earlier
                then pure $ ExVar (ExVar' var2)
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
              ExVar (ExVar' var2) →
                if origVar1 == ExVar' var2
                  then pure ()
                  else
                    sendIO (readIORef var2) >>= \case
                      Left val' → do
                        nesting ← length <$> ask @BindsT
                        instMeta (scope1, t1) origVar1 $ unport val' nesting
                      _ → r
              _ → r

withMono ∷ (Has Solve sig m) ⇒ ((TermT → m TermT) → a → m a) → TermT → (ExVar' → (Int, Maybe PortableTermT) → m a) → (TermT → m a) → m a
withMono tmap = \a onMeta onOther → withMono' onMeta onOther a
 where
  withMono' onMeta onOther = \wrapped → do
    nesting ← length <$> ask @BindsT
    let port = PortableTerm nesting
    case wrapped of
      Sorry _ v → withMono' onMeta onOther v
      ExVar (ExVar' var) →
        sendIO (readIORef var) >>= \case
          Left v → withMono' onMeta onOther $ unport v nesting
          Right (_, scope, t) → onMeta (ExVar' var) (scope, t)
      Quantification Forall _name kind v → scoped' tmap do
        ty ← pushExVar $ Just $ PortableTerm nesting kind
        pure $ withMono' onMeta onOther =<< normalize (nestedNormBinds nesting [Just $ port ty]) v
      Quantification Exists _name kind v → scoped' tmap do
        ty ← pushUniVar $ port kind
        pure $ withMono' onMeta onOther =<< normalize (nestedNormBinds nesting [Just $ port ty]) v
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
withLookupField ∷ (Has Solve sig m) ⇒ (LookupRes → m a) → ((TermT → m TermT) → a → m a) → Bool → TermT → ([(TermT, TermT)], Maybe TermT) → m a
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
              (mScope, Just (PortableTerm origin (App (Builtin Row) mT))) →
                beforeEx mScope var do
                  rest' ← pushExVar (Just $ PortableTerm origin $ rowOf mT)
                  val' ← pushExVar (Just $ PortableTerm origin mT)
                  writeMeta (mScope, Just $ PortableTerm origin $ rowOf mT) var $ FieldsLit FRow [(needle, val')] $ Just rest'
                  pure $ cont $ LookupFound val' (toList prev, Just rest')
              _ → notARow $ ExVar var
            else const $ cont LookupMissing
      )
      \case
        FieldsLit FRow vals rest → rec prev (vals, rest)
        x → stackError $ "lookupField todo " <> pTerm' x
    ((name, val) : xs, rest) →
      isEq needle name >>= \case
        EqYes → cont $ LookupFound val (toList prev <> xs, rest)
        EqUnknown → cont LookupUnknown
        EqNot → rec (prev |> (name, val)) (xs, rest)

typOfBuiltin ∷ BuiltinT → PortableTermT
typOfBuiltin =
  PortableTerm 0 . \case
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
    ((ExVar a), bT) → subtypeMeta a bT
    (aT, (ExVar b)) → subtypeMeta b aT
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
        (ExVar a'', _) → subtypeMeta a'' b
        (_, ExVar b'') → subtypeMeta b'' a
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
    (ExVar (ExVar' a)) →
      sendIO (readIORef a) >>= \case
        Left i → do
          nesting ← currNesting
          unwrapExs $ unport i nesting
        _ → pure inp
    _ → pure inp
  subtypeMeta (ExVar' a) bT =
    sendIO (readIORef a) >>= \case
      Left _ → error "Impossible"
      Right (_, aScope, aT) → instMeta (aScope, aT) (ExVar' a) bT

runSolveM ∷ (Applicative m) ⇒ ReaderC BindsT (StateC MetaVarsT (FreshC (ErrorC (Doc AnsiStyle) m))) a → m (Either (Doc AnsiStyle) a)
runSolveM =
  runError (pure . Left) (pure . Right)
    . evalFresh 0
    . evalState @MetaVarsT mempty
    . runReader @BindsT []

checkFile ∷ FilePath → IO ()
checkFile file = do
  term ← parseFile file
  (stacks, res) ← runStackAccC $ runSolveM $ infer term Infer
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
  res ← runStackPrintC $ runSolveM $ infer term Infer
  render case res of
    Left e → annotate (color Red) "error: " <> e
    Right r → pTerm' r
-}

main ∷ IO ()
main = pure ()
