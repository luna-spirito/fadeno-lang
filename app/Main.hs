{-# LANGUAGE UndecidableInstances #-}

module Main where

import Control.Algebra
import Control.Carrier.Error.Church (ErrorC, runError)
import Control.Carrier.Fresh.Church (FreshC, evalFresh)
import Control.Carrier.Reader (ReaderC, runReader)
import Control.Carrier.State.Church (StateC, execState, runState)
import Control.Carrier.Writer.Church (WriterC, execWriter, runWriter)
import Control.Effect.Error (Error, Throw, throwError)
import Control.Effect.Fresh (Fresh, fresh)
import Control.Effect.Lift (Lift, sendIO)
import Control.Effect.Reader (Reader, ask, local)
import Control.Effect.State (get, put)
import Control.Effect.Writer (Writer, censor, listen, tell)
import Data.ByteString.Char8 (pack)
import Data.List (sortBy)
import Data.RRBVector (Vector, deleteAt, ifoldr, viewl, (!?), (<|))
import GHC.Exts (IsList (..))
import Normalize (EqRes (..), Resolved, concat, isEq', nested, nestedBy, normalize, resolve, resolve', rewrite, runSeqResolve, termQQ, withResolved)
import Parser (BlockT (..), BuiltinT (..), ExVarId (..), Ident (..), Lambda (..), Quantifier (..), TermT (..), Vector' (..), builtinsList, identOfBuiltin, pIdent, pTerm', parseFile, recordOf, render, rowOf)
import Prettyprinter (Doc, annotate, group, indent, line, nest, pretty, (<+>))
import Prettyprinter.Render.Terminal (AnsiStyle, Color (..), color)
import RIO hiding (Reader, Vector, ask, concat, filter, link, local, runReader, toList)
import RIO.HashMap qualified as HM

-- TODO: You currently don't perform `resolve` in terms processed...
-- This is probably an error.

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

type Solve = Writer Resolved :+: Fresh :+: Error (Doc AnsiStyle) :+: StackLog

writeMeta ∷ (Has Solve sig m) ⇒ Ident → ExVarId → Maybe TermT → TermT → m ()
writeMeta n var tyM val = do
  stackLog $ pIdent n <+> ":=" <+> pTerm' val
  for_ tyM $ infer [] val . Check
  tell $ HM.singleton var val

scopedVar ∷ (Has Solve sig m) ⇒ ((TermT → m TermT) → a → m a) → m a → m a
scopedVar mapTerm act = do
  (resolved, res) ← intercept @Resolved act
  let unnest original =
        rewrite
          (const (+ 1))
          (+ 1)
          ( \term locs → case term of
              Var i | i == locs → stackError $ "Var leaked in " <> pTerm' original
              Var i | i > locs → pure $ Just $ Var $ i - 1
              _ → pure Nothing
          )
          0
          original
  tell =<< for resolved unnest
  mapTerm unnest res

scopedUniVar ∷ (Has Solve sig m) ⇒ ((TermT → m TermT) → a → m a) → Int → m a → m a
scopedUniVar mapTerm uni1 act = do
  (resolved, res) ← listen @Resolved act
  let ensureNotOcc original =
        rewrite
          (const id)
          id
          ( \term () → case term of
              UniVar _ uni2 _ | uni1 == uni2 → stackError $ "UniVar leaked in " <> pTerm' original
              _ → pure Nothing
          )
          ()
          original
  for_ resolved ensureNotOcc
  mapTerm ensureNotOcc res

freshIdent ∷ (Has Solve sig m) ⇒ m Ident
freshIdent = (`Ident` False) . ("/" <>) . pack . show <$> fresh

scopedExVar ∷ (Has Solve sig m) ⇒ ((TermT → m TermT) → a → m a) → Int → m a → m a
scopedExVar mapTerm ex1 act = do
  (resolved, res) ← intercept @Resolved act
  let isOfEx1 (ExVarId x) = (== ex1) $ fst $ fromMaybe (error "impossible") $ viewl x
      resolved' = HM.filterWithKey (\k _ → not $ isOfEx1 k) resolved
  for_ resolved' \original →
    rewrite
      (const id)
      id
      ( \term () → case term of
          ExVar _ ex2 _
            | isOfEx1 ex2 →
                stackError $ "ExVar leaked in " <> pTerm' original
          _ → pure Nothing
      )
      ()
      original
  tell resolved'
  mapTerm
    ( \outT → do
        stackLog $ pTerm' outT
        let exsInOut =
              sortBy (\a b → fst a `compare` fst b)
                $ toList
                $ runIdentity
                $ execWriter @(HashMap ExVarId (Maybe TermT))
                $ rewrite
                  (const id)
                  id
                  ( \term () → case term of
                      ExVar _ ex ty
                        | isOfEx1 ex →
                            -- TODO: Bug with `ty`. Either unnest it, or think out of a better implementation overall.
                            tell @(HashMap ExVarId (Maybe TermT)) [(ex, ty)] *> pure Nothing
                      _ → pure Nothing
                  )
                  ()
                  outT
            rewriteExVar ex with0 =
              runIdentity
                . rewrite
                  (const nested)
                  nested
                  ( \term with → pure $ case term of
                      ExVar _ ex' _ | ex == ex' → Just with
                      _ → Nothing
                  )
                  with0
         in foldM
              ( \acc (ex, tyM) →
                  case tyM of
                    Nothing → do
                      uN ← freshIdent
                      n ← freshIdent
                      pure
                        $ Quantification Forall uN (Builtin U32)
                        $ Lambda
                        $ Quantification Forall n (App (Builtin TypePlus) (Var 0))
                        $ Lambda
                        $ rewriteExVar ex (Var 0)
                        $ nestedBy 2 acc
                    Just ty → do
                      n ← freshIdent
                      pure $ Quantification Forall n ty $ Lambda $ rewriteExVar ex (Var 0) $ nested acc
              )
              outT
              exsInOut
    )
    res

withMono ∷
  (Has Solve sig m) ⇒
  ((TermT → m TermT) → a → m a) →
  -- | onMeta
  ReaderC (Ident, ExVarId, Maybe TermT) m TermT →
  -- | onOther
  (Resolved → TermT → m a) →
  TermT →
  m a
withMono mapTerm onMeta onOther = go
 where
  go = \case
    Sorry _ v → go v
    ExVar n i ty → do
      val ← runReader (n, i, ty) onMeta
      runSeqResolve do
        withResolved \_ → writeMeta n i ty val
        withResolved \exs → onOther exs val
    Quantification Forall n xTy x → do
      exId ← fresh
      scopedExVar mapTerm exId $ go $ normalize [Just $ ExVar n (ExVarId [exId]) $ Just xTy] $ unLambda x
    Quantification Exists n xTy x → do
      uniId ← fresh
      scopedUniVar mapTerm uniId $ go $ normalize [Just $ UniVar n uniId xTy] $ unLambda x
    r → onOther [] r

subExVar ∷ (Has (Reader (Ident, ExVarId, Maybe TermT) :+: Fresh) sig m) ⇒ ByteString → Maybe TermT → m TermT
subExVar subName subTy = do
  subI ← fresh
  (Ident baseName _, ExVarId baseI, _ ∷ Maybe TermT) ← ask
  -- TODO: check that such ignore doesn't destroy anything.
  pure $ ExVar (Ident (baseName <> "/" <> subName) False) (ExVarId $ baseI <> [subI]) subTy

isEqUnify ∷ (Has Solve sig m) ⇒ TermT → TermT → m EqRes
isEqUnify = isEq' instMeta

data LookupRes a
  = LookupFound !a
  | LookupMissing !(Vector' TermT) -- Visited keys
  | LookupUnknown
  deriving (Show)

{- | Accepts `tag`, `row` and `record`. Provides access to the field `tag` in `row`,
performs refines if necessary.
-}
rowGet ∷ ∀ sig m a. (Has Solve sig m) ⇒ ((TermT → m TermT) → a → m a) → TermT → (TermT → m a) → TermT → TermT → m (LookupRes a)
rowGet mapTerm tag cont = go
 where
  notARow x = stackError $ "Not a row:" <+> pTerm' x
  go ∷ TermT → TermT → m (LookupRes a)
  go row record =
    withMono
      ( \f → \case
          LookupFound a → LookupFound <$> mapTerm f a
          LookupMissing (Vector' keys) → LookupMissing . Vector' <$> traverse f keys
          LookupUnknown → pure LookupUnknown
      )
      ( do
          (_ ∷ Ident, _ ∷ ExVarId, ty) ← ask
          case ty of
            Just (App (Builtin Row) mT) → do
              h ← subExVar "head" (Just mT)
              t ← subExVar "tail" (Just $ rowOf mT)
              pure $ Concat h (Right t)
            _ → do
              (n, var, _ ∷ Maybe TermT) ← ask
              notARow $ ExVar n var ty
      )
      ( \_ → \case
          RecordLit (Vector' l) → case viewl l of
            Nothing → pure $ LookupMissing []
            Just ((n, v), rest) → runSeqResolve do
              eqTag ← withResolved \_ → isEqUnify n tag
              case eqTag of
                EqYes → LookupFound <$> withResolved \exs → cont (resolve exs v)
                EqNot → do
                  inRest ← withResolved \exs → go (RecordLit (Vector' $ bimap (resolve exs) (resolve exs) <$> rest)) record
                  case inRest of
                    LookupFound res → pure $ LookupFound res
                    LookupMissing (Vector' fi) → withResolved \exs → pure $ LookupMissing $ Vector' $ resolve exs n <| fi
                    LookupUnknown → pure LookupUnknown
                EqUnknown → pure LookupUnknown
          Concat l rE → runSeqResolve do
            inL ← withResolved \exs → go (resolve exs l) record
            case inL of
              LookupMissing visited1 → do
                let
                  select f = normalize [] $ App (App (Builtin f) $ ListLit $ visited1) record
                  recordL = select RecordKeepFields
                  recordR = select RecordDropFields
                r' ← withResolved \exs → case rE of
                  Left (_, r) → go (normalize [Just recordL] $ resolve exs $ unLambda r) recordR
                  Right r → go (resolve exs r) $ recordR
                case r' of
                  LookupMissing visited2 → pure $ LookupMissing $ visited1 <> visited2
                  o → pure o
              o → pure o
          x → notARow x
      )
      row

unifyFields ∷ (Has Solve sig m) ⇒ Vector' (TermT, TermT) → StateC (Maybe TermT) m ()
unifyFields fi = runSeqResolve $ for_ fi \(_fieldName, fieldValue) → do
  fieldValue' ← withResolved \exs → pure $ resolve exs fieldValue
  currentUnifiedTyM ← get
  withResolved \_ → case currentUnifiedTyM of
    Nothing → put $ Just fieldValue'
    Just currentUnifiedTy → runSeqResolve do
      withResolved \_ → subtype fieldValue' currentUnifiedTy
      withResolved \exs → put $ Just $ resolve exs currentUnifiedTy

withKnownFields ∷ (Has Solve sig m) ⇒ ((TermT → m TermT) → a → m a) → TermT → (Vector' (TermT, TermT) → m a) → m a
withKnownFields tmap t f =
  withMono
    tmap
    (stackError "Unknown shape")
    ( \_ → \case
        RecordLit x → f x
        _ → stackError "Not a record"
    )
    t

bottom ∷ TermT
bottom = [termQQ| forall (u : U32) (a : Type+ u). a |]

bottomRow ∷ TermT
bottomRow = [termQQ| forall (u : U32) (row : Row (Type+ u)). row |]

ensureIsType ∷ (Has Solve sig m) ⇒ TermT → m TermT
ensureIsType t = do
  withMono
    id
    (lift fails)
    ( \_ → \ty → case ty of
        App (Builtin TypePlus) _ → pure ty
        App (Builtin Row) _ → pure ty
        App (Builtin Record) r →
          rowOf <$> withKnownFields id r \fields →
            fromMaybe bottomRow <$> execState Nothing (unifyFields fields)
        _ → fails
    )
    t
 where
  fails = stackError $ pTerm' t <> " is not a type?"

data InferMode a where
  Infer ∷ InferMode TermT
  Check ∷ TermT → InferMode ()

pMode ∷ InferMode a → Doc AnsiStyle
pMode = \case
  Infer → "_"
  Check t → pTerm' t

nestMode ∷ InferMode a → InferMode a
nestMode = \case
  Infer → Infer
  Check x → Check $ nested x

mapTermFor ∷ (Applicative f) ⇒ InferMode a → ((TermT → f TermT) → a → f a)
mapTermFor = \case
  Infer → id
  Check _ → const pure

-- TODO: We could implement "bindings update" as an effect.
-- Performance improvements over rewriting all the bindings.

resolveBinds ∷ HashMap ExVarId TermT → Vector (Maybe TermT, TermT) → Vector (Maybe TermT, TermT)
resolveBinds (HM.null → True) = id
resolveBinds exs = fmap $ bimap id $ resolve exs

resolveMode ∷ HashMap ExVarId TermT → InferMode a → InferMode a
resolveMode exs = \case
  Infer → Infer
  Check a → Check $ resolve exs a

insertBinds ∷ (Maybe TermT, TermT) → Vector (Maybe TermT, TermT) → Vector (Maybe TermT, TermT)
insertBinds new old = new <| (bimap (nested <$>) nested <$> old)

-- | Either infers a normalized type for the value and context, or checks a value against the normalized type.
infer ∷ ∀ sig m a. (Has Solve sig m) ⇒ Vector (Maybe TermT, TermT) → TermT → InferMode a → m a
infer binds = \t mode → stackScope ("<" <> group (pTerm' t) <> "> : " <> pMode mode) $ infer' t mode
 where
  -- Here, we will convert Checks to Infers.
  -- However, converting Infer to a Check when checking a term is hereby declared a deadly sin.
  infer' ∷ TermT → InferMode a → m a
  infer' = curry \case
    (term, Check (Quantification Forall n xTy yT)) → do
      uniId ← fresh
      scopedUniVar (const pure) uniId $ infer binds term $ Check $ normalize [Just $ UniVar n uniId xTy] $ unLambda yT
    -- TODO: breaks.
    -- (term, Check ((Quantification Exists xName Ty yT))) → scoped_ do -- TODO: not just for Ty!
    --   x' ← pushExVar
    --   yT' ← normalize (HM.singleton xName x') yT
    --   infer ctx term $ Check $ yT'
    (Block (BlockLet name tyM val into), mode) → runSeqResolve do
      ty ← withResolved \_ → stackScope ("let" <+> pIdent name) case tyM of
        Nothing → infer binds val Infer
        Just ty → do
          -- TODO: check ty' to be a type?
          -- EDIT: typechecking is undecidable... so... uh... no?
          let ty' = normalize (fst <$> binds) ty
          infer binds val $ Check ty'
          pure ty'
      let val' = normalize (fst <$> binds) val
          withLog act = case (unLambda into) of
            Block{} → act
            _ → stackScope "in" act
      withResolved \exs →
        withLog
          $ scopedVar (mapTermFor mode)
          $ infer (insertBinds (Just val', ty) binds) (unLambda into)
          $ nestMode
          $ resolveMode exs mode
    (Lam _arg bod, Infer) → do
      inT ← fresh
      n ← freshIdent
      let inT' = ExVar n (ExVarId [inT]) Nothing
      scopedExVar id inT $ runSeqResolve do
        outT ← withResolved \_ →
          scopedVar id
            $ infer (insertBinds (Nothing, inT') binds) (unLambda bod) Infer
        withResolved \exs → pure $ Pi (resolve exs inT') $ Right outT
    (Op a _op b, Infer) → runSeqResolve do
      withResolved \_ → infer binds a $ Check $ Builtin U32
      withResolved \exs → infer (resolveBinds exs binds) b $ Check $ Builtin U32
      pure $ Builtin U32
    (Lam _ bod, Check (Pi inT outT)) → do
      case outT of
        Right outT' → scopedVar (const pure) $ infer (insertBinds (Nothing, inT) binds) (unLambda bod) $ Check outT'
        Left (_, outT') → do
          n ← freshIdent
          u ← fresh
          let var = UniVar n u inT
          scopedVar (const pure)
            $ scopedUniVar (const pure) u
            $ infer (insertBinds (Just var, inT) binds) (unLambda bod)
            $ Check
            $ normalize [Just var]
            $ unLambda outT'
    (App (App (Builtin RecordGet) tag) record, mode) → runSeqResolve do
      recordT ← withResolved \_ → infer binds record Infer
      withResolved \exs → infer (resolveBinds exs binds) tag $ Check $ Builtin Tag
      withResolved \exs →
        let
          body row extraExs = do
            let exs' = exs <> extraExs
            res ←
              rowGet
                (mapTermFor mode)
                tag
                ( \ty → case mode of
                    Infer → pure ty
                    Check ty2 → subtype ty $ resolve exs' ty2
                )
                row
                record
            case res of
              LookupFound x → pure x
              _ → stackError "App RecordGet"
         in
          withMono
            (mapTermFor mode)
            ( do
                tVar ← subExVar "t" Nothing
                rowVar ← subExVar "row" $ Just $ rowOf tVar
                pure $ recordOf rowVar
            )
            ( \exs2 → \case
                App (Builtin Record) row → body row exs2
                _ → stackError "Not a record"
            )
            (resolve exs recordT)
    (App f a, Infer) → runSeqResolve do
      fTy ← withResolved \_ → infer binds f Infer
      withResolved \exs →
        withMono
          id
          (Pi <$> subExVar "in" Nothing <*> (Right <$> subExVar "out" Nothing))
          ( \exs2 → \case
              Pi inT outTE → runSeqResolve do
                withResolved \_ → infer (resolveBinds (exs <> exs2) binds) a $ Check $ inT
                withResolved \exs3 → pure $ case outTE of
                  Left (_, outT) → resolve exs3 $ normalize [Just $ normalize (fst <$> binds) a] $ unLambda outT
                  Right outT → resolve exs3 outT
              t → stackError $ "inferApp " <> pTerm' t
          )
          fTy
    (RecordLit flds, Infer) → runSeqResolve do
      rowFields ← for flds \(n, v) → do
        withResolved \exs → infer (resolveBinds exs binds) n $ Check $ Builtin Tag
        vTy ← withResolved \exs → infer (resolveBinds exs binds) v Infer
        pure (n, vTy)
      pure $ recordOf $ RecordLit rowFields
    (ListLit values, Infer) →
      App (Builtin List) . fromMaybe bottom . fst <$> execState (Nothing, binds) do
        for_ values \v → do
          (unifiedTy0M, binds0) ← get
          runSeqResolve do
            unifiedTy ← withResolved \_ → case unifiedTy0M of
              Nothing → infer binds v Infer
              Just unifiedTy0 → runSeqResolve do
                withResolved \_ → infer binds v (Check unifiedTy0)
                withResolved \exs → pure (resolve exs unifiedTy0)
            withResolved \exs → put (Just unifiedTy, resolveBinds exs binds0)
    (Concat l rE, Infer) →
      let
        -- TODO: what should be here?
        withKnown t f = withMono id (stackError "TODO Concat infer") (\_exs → f) t
        withKnownFields' = withKnownFields id
        concatT lT rT = case (lT, rT, rE) of
          (App (Builtin Record) lR, App (Builtin Record) rR, Right _) → pure $ recordOf $ concat lR rR
          (App (Builtin Record) lR, App (Builtin Record) rR, Left (_, Lambda _)) →
            rowOf <$> withKnownFields' lR \lR' → withKnownFields' rR \rR' →
              fromMaybe bottomRow
                <$> execState
                  Nothing
                  ( runSeqResolve do
                      withResolved \_ → unifyFields lR'
                      withResolved \exs → unifyFields $ bimap (resolve exs) (resolve exs) <$> rR'
                  )
          (App (Builtin Row) lRT, App (Builtin Record) rR, _) → rowOf <$> withKnownFields' rR \rR' → fromMaybe (error "impossible") <$> execState (Just lRT) (unifyFields rR')
          (App (Builtin Record) lR, App (Builtin Row) rRT, _) → rowOf <$> withKnownFields' lR \lR' → fromMaybe (error "impossible") <$> execState (Just rRT) (unifyFields lR')
          (App (Builtin Row) lRT, App (Builtin Row) rRT, _) → runSeqResolve do
            withResolved \_ → subtype rRT lRT
            withResolved \exs → pure $ resolve exs lRT
          _ → stackError "Concat of non-records"
       in
        runSeqResolve do
          lT ← withResolved \_ → infer binds l Infer
          rT ← withResolved \exs →
            let binds' = resolveBinds exs binds
             in either
                  ( \(_, r) →
                      scopedVar id
                        $ infer
                          (insertBinds (Nothing, recordOf $ normalize (fst <$> binds) l) binds')
                          (unLambda r)
                          Infer
                  )
                  (\r → infer binds' r Infer)
                  rE
          withResolved \exs →
            withKnown (resolve exs lT) \lT' → withKnown rT \rT' → concatT lT' rT'
    (NatLit _, Infer) → pure $ Builtin U32
    (TagLit _, Infer) → pure $ Builtin Tag
    (BoolLit _, Infer) → pure $ Builtin Bool
    (Var i, Infer) → case binds !? i of
      Nothing → stackError $ "Unknown var @" <> pretty i
      Just (_, ty) → pure ty
    -- TODO: Support checks...
    (Quantification _ _name kind ty, Infer) → do
      res ← scopedVar id $ infer (insertBinds (Nothing, normalize (fst <$> binds) kind) binds) (unLambda ty) Infer
      ensureIsType res
    -- (Pi inNameM x y, Check (App (Builtin Type) u)) → do
    --   infer x $ Check $ typOf u
    --   (if isJust inNameM then local @BindsT (|> (Nothing, PortableTerm valNesting0 x)) else id)
    --     $ infer y
    --     $ Check
    --     $ typOf u
    (Pi inTy (Right outTy), Infer) → runSeqResolve do
      inTyTy ← withResolved \_ → ensureIsType =<< infer binds (normalize (fst <$> binds) inTy) Infer
      withResolved \exs →
        let binds' = resolveBinds exs binds
         in infer binds' (normalize (fst <$> binds') outTy) $ Check inTyTy
      withResolved \exs → pure (resolve exs inTyTy)
    (Builtin x, Infer) → pure $ typOfBuiltin x
    (BuiltinsVar, Infer) →
      pure
        $ App (Builtin Record)
        $ RecordLit
        $ Vector'
        $ (\b → (TagLit $ identOfBuiltin b, typOfBuiltin b))
        <$> builtinsList
    (UniVar _n _i ty, Infer) → pure ty
    (ExVar _n _i (Just ty), Infer) → pure ty
    (k, Infer) → stackError $ pretty $ show k
    (term, Check c) → stackScope ("check via infer" <+> pTerm' term <+> ":" <+> pTerm' c) $ runSeqResolve do
      ty ← withResolved \_ → infer binds term Infer
      withResolved \exs → subtype (resolve exs ty) $ resolve exs c

typOfBuiltin ∷ BuiltinT → TermT
typOfBuiltin =
  \case
    U32 → [termQQ| Type+ 0 |]
    Tag → [termQQ| Type+ 0 |]
    Bool → [termQQ| Type+ 0 |]
    Row → [termQQ| forall (u : U32). Type+ u -> Type+ u |]
    Record → [termQQ| forall (u : U32). Row (Type+ u) -> Type+ u |]
    List → [termQQ| forall (u : U32). Type+ u -> Type+ u |]
    TypePlus → [termQQ| u : U32 -> Type+ (u + 1) |]
    Eq → [termQQ| forall (u : U32) (a : Type+ u). a -> a -> Type+ u |]
    Refl → [termQQ| forall (u : U32) (a : Type+ u) (x : a). Eq x x |]
    RecordGet →
      [termQQ|
        forall (u : U32) (row : Row (Type+ u)) (t : Type+ u).
          tag : Tag ->
          record : Record ({(tag) = t} \/ row) ->
          t
      |]
    -- TODO: Better type
    RecordKeepFields → [termQQ| forall (u : U32) (row : Row (Type+ u)). exists (new-row : Row (Type+ u)). List Tag -> Record row -> Record new-row |]
    RecordDropFields → [termQQ| forall (u : U32) (row : Row (Type+ u)). exists (new-row : Row (Type+ u)). List Tag -> Record row -> Record new-row |]
    ListLength → [termQQ| forall (u : U32) (a : Type+ u). List a -> U32 |]
    ListIndexL → [termQQ| forall (u : U32) (a : Type+ u). l : List a -> Fin (list-length l) -> a |]
    NatFold → [termQQ| forall (u : U32). Acc : (U32 -> Type+ u) -> n : U32 -> Acc 0 -> (i : Fin n -> Acc i -> Acc (i + 1)) -> Acc n |]

instMeta ∷ ∀ sig m. (Has Solve sig m) ⇒ Ident → ExVarId → Maybe TermT → TermT → m ()
instMeta = (\f a b c d → stackScope "instMeta" $ f a b c d) \n1 (ExVarId var1) t1 →
  let instMeta' ∷ TermT → m TermT
      instMeta' = \case
        Sorry _ x → instMeta' x
        ExVar n2 (ExVarId var2) t2 →
          if var2 <= var1
            then pure $ ExVar n2 (ExVarId var2) t2
            else do
              u ← fresh
              n ← freshIdent
              let var1R = ExVar n (ExVarId $ var1 <> [u]) t2
              writeMeta n2 (ExVarId var2) t2 var1R
              pure $ var1R
        uni@(UniVar _ uni2 _)
          | [uni2] <= var1 → pure uni
        App f a → runSeqResolve do
          f' ← withResolved \_ → instMeta' f
          a' ← withResolved \exs → instMeta' $ resolve exs a
          pure $ App f' a'
        RecordLit flds → RecordLit <$> traverse (bitraverse instMeta' instMeta') flds
        Concat a b → runSeqResolve do
          a' ← withResolved \_ → instMeta' a
          b' ← withResolved \exs →
            either
              (\(n, b'') → fmap (Left . (n,) . Lambda) $ scopedVar id $ instMeta' $ resolve' 1 exs $ unLambda b'')
              (fmap Right . instMeta' . resolve exs)
              b
          pure $ Concat a' b'
        Var x → pure $ Var x -- TODO: I hope this is correct, but needs to be rechecked.
        Builtin x → pure $ Builtin x
        NatLit x → pure $ NatLit x
        Pi inT outT →
          runSeqResolve
            $ Pi
            <$> (withResolved \_ → instMeta' inT)
            <*> withResolved (\exs → either (\(n, v) → Left . (n,) . Lambda <$> instMeta' (resolve' 1 exs $ unLambda v)) (fmap Right . instMeta' . resolve exs) outT)
        Op a op b → do
          a' ← instMeta' a
          b' ← instMeta' b
          pure $ Op a' op b'
        x → stackError $ "instMeta (of" <+> pretty (tshow $ ExVarId var1) <> ")" <+> pTerm' x
   in \val →
        let r = writeMeta n1 (ExVarId var1) t1 =<< instMeta' val
         in case val of
              ExVar _ var2 _ →
                if var2 == ExVarId var1
                  then pure ()
                  else r
              _ → r

-- | a <: b Check if type `a` is a subtype of type `b`.
subtype ∷ ∀ sig m. (Has Solve sig m) ⇒ TermT → TermT → m ()
subtype = \a b →
  stackScope (pTerm' a <+> annotate (color Cyan) "<:" <+> pTerm' b) $ subtype' a b
 where
  -- Helper to call instMeta for subtyping existentials.
  subtypeMeta ∷ Ident → ExVarId → Maybe TermT → TermT → m ()
  subtypeMeta exN exId exTyM otherT = instMeta exN exId exTyM otherT

  -- Core subtyping logic based on the structure of the resolved types.
  subtype' ∷ TermT → TermT → m ()
  subtype' = curry \case
    -- Existential Variables (?a <: ?b, ?a <: T, T <: ?a)
    (ExVar _ ex1 _, ExVar _ ex2 _) | ex1 == ex2 → pure ()
    (ExVar n1 ex1 ty1, t2) → subtypeMeta n1 ex1 ty1 t2
    (t1, ExVar n2 ex2 ty2) → subtypeMeta n2 ex2 ty2 t1
    -- Universal Variables (u1 <: u2) - Must be identical.
    (UniVar _ id1 _, UniVar _ id2 _) | id1 == id2 → pure ()
    -- T <: Forall x:K. Body  => Introduce UniVar for x
    (t, Quantification Forall n k body) → do
      uniId ← fresh
      scopedUniVar (const pure) uniId
        $ subtype t
        $ normalize [Just $ UniVar n uniId k]
        $ unLambda body

    -- Exists x:K. Body <: T => Introduce UniVar for x
    (Quantification Exists n k body, t) → do
      uniId ← fresh
      scopedUniVar (const pure) uniId
        $ subtype (normalize [Just $ UniVar n uniId k] $ unLambda body) t

    -- Forall x:K. Body <: T => Introduce ExVar for x
    (Quantification Forall n k body, t) → do
      exId ← fresh
      scopedExVar (const pure) exId
        $ subtype (normalize [Just $ ExVar n (ExVarId [exId]) $ Just k] $ unLambda body) t

    -- T <: Exists x:K. Body => Introduce ExVar for x
    (t, Quantification Exists n k body) → do
      exId ← fresh
      scopedExVar (const pure) exId
        $ subtype t
        $ normalize [Just $ ExVar n (ExVarId [exId]) $ Just k]
        $ unLambda body

    -- Function Types (Πx:T1.U1 <: Πy:T2.U2)
    (Pi inT1 outT1E, Pi inT2 outT2E) → runSeqResolve do
      -- Input types are contravariant (T2 <: T1)
      withResolved \_ → subtype inT2 inT1
      -- Output types are covariant
      withResolved \exs → case (outT1E, outT2E) of
        -- Both non-dependent
        (Right outT1, Right outT2) → subtype (resolve exs outT1) (resolve exs outT2)
        -- Both dependent
        (Left (_n1, lbd1), Left (n2, lbd2)) → do
          uniId ← fresh
          -- Introduce UniVar with the *supertype's* input type (inT2)
          scopedUniVar (const pure) uniId do
            let var = UniVar n2 uniId inT2 -- Use common name/type for substitution
            let body1 = resolve exs $ normalize [Just var] $ unLambda lbd1
            let body2 = resolve exs $ normalize [Just var] $ unLambda lbd2
            subtype body1 body2
        -- Mixed cases are not subtypes of each other
        _ → stackError "Cannot subtype mixed dependent/non-dependent Pi types"

    -- Builtin Types (must be identical)
    (Builtin a, Builtin b) | a == b → pure ()
    -- Type Universes (Type L1 <: Type L2 where L1 <= L2)
    (App (Builtin TypePlus) a, App (Builtin TypePlus) b) → do
      case (a, b) of
        (NatLit x, NatLit y) | x <= y → pure ()
        (NatLit 0, _) → pure ()
        -- If one level is existential, unify it with the other level constraint.
        (ExVar nA exA tyA, lvl2) → subtypeMeta nA exA tyA lvl2
        (lvl1, ExVar nB exB tyB) → subtypeMeta nB exB tyB lvl1
        _ → runSeqResolve do
          r ← withResolved \_ → isEqUnify a b
          case r of
            EqYes → pure ()
            _ → withResolved \exs → stackError $ "Cannot subtype universes with levels:" <+> pTerm' (resolve exs a) <+> "<=" <+> pTerm' (resolve exs b)

    -- Record/Row types (requires structural subtyping logic)
    (App (Builtin Record) row1, App (Builtin Record) row2) → subtype row1 row2 -- Delegate to row subtyping
    (App (Builtin Row) fields1, App (Builtin Row) fields2) → subtype fields1 fields2
    (App (Builtin Record) fieldsVal, App (Builtin Row) fieldsTy) →
      withKnownFields (const pure) fieldsVal \fi →
        runState (\_ _ → pure ()) (Just fieldsTy) $ unifyFields fi
    (RecordLit (Vector' fields1), RecordLit fields2) →
      let
        fields1Drop fields1' name ty =
          runSeqResolve
            $ ifoldr
              ( \i (name1, ty1) rec → do
                  eqName ← withResolved \exs → isEqUnify (resolve exs name) (resolve exs name1)
                  case eqName of
                    EqYes → do
                      withResolved \exs → subtype (resolve exs ty1) (resolve exs ty)
                      withResolved \exs → pure $ bimap (resolve exs) (resolve exs) <$> deleteAt i fields1'
                    EqUnknown → stackError "Unable to check field equality when subtyping"
                    EqNot → rec
              )
              (stackError "Missing field from left side when subtyping")
              fields1'
       in
        runSeqResolve
          $ foldM_
            (\fields1' (name, ty) → withResolved \exs → fields1Drop fields1' (resolve exs name) (resolve exs ty))
            fields1
            fields2
    -- n : l1 \/ r1  <:  n : l2 \/ r2
    (Concat l1 (Left (n, lr1)), Concat l2 (Left (_, lr2))) → runSeqResolve do
      withResolved \_ → subtype l1 l2
      uniId ← fresh
      withResolved \exs → scopedUniVar (const pure) uniId do
        let var = UniVar n uniId l1
        let body1 = resolve exs $ normalize [Just var] $ unLambda lr1
        let body2 = resolve exs $ normalize [Just var] $ unLambda lr2
        subtype body1 body2

    -- App f1 a1 <: App f2 a2
    (App f1 a1, App f2 a2) → runSeqResolve do
      eqF ← withResolved \_ → isEqUnify f1 f2
      case eqF of
        EqYes → do
          eqA ← withResolved \exs → isEqUnify (resolve exs a1) (resolve exs a2)
          case eqA of
            EqYes → pure ()
            _ → stackError $ "Cannot subtype applications with different arguments:" <+> pTerm' a1 <+> "vs" <+> pTerm' a2
        _ → stackError $ "Cannot subtype applications with different functions:" <+> pTerm' f1 <+> "vs" <+> pTerm' f2
    -- Catch-all: if no rule matches, they are not subtypes
    (t1, t2) → stackError $ "Subtype check failed, no rule applies for:" <+> pTerm' t1 <+> "<:" <+> pTerm' t2

runSolveM ∷ (Applicative m) ⇒ WriterC Resolved (FreshC (ErrorC (Doc AnsiStyle) m)) a → m (Either (Doc AnsiStyle) a)
runSolveM =
  runError (pure . Left) (pure . Right)
    . evalFresh 0
    . runWriter (const pure) -- TODO: alert on unhandled?

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
