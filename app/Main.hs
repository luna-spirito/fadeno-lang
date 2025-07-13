{-# LANGUAGE UndecidableInstances #-}

module Main where

import Control.Algebra
import Control.Carrier.Error.Church (ErrorC, runError)
import Control.Carrier.Fresh.Church (FreshC, evalFresh)
import Control.Carrier.Reader (ReaderC, runReader)
import Control.Carrier.State.Church (StateC, execState, runState)
import Control.Carrier.Writer.Church (WriterC, execWriter, runWriter)
import Control.Effect.Error (Error, throwError)
import Control.Effect.Fresh (Fresh, fresh)
import Control.Effect.Lift (Lift, sendIO)
import Control.Effect.Reader (Reader, ask, local)
import Control.Effect.State (get, put)
import Control.Effect.Writer (Writer, censor, listen, tell)
import Data.ByteString.Char8 (pack)
import Data.List (find, sortBy)
import Data.RRBVector (Vector, deleteAt, ifoldr, viewl, (!?), (<|))
import GHC.Exts (IsList (..))
import Normalize (Binding, EqRes (..), Resolved, concat, insertBinds, isEq', nested, nestedBy, normalize, numDecDispatch, resolve, resolve', rewrite, runSeqResolve, termQQ, withResolved)
import Parser (Bits (..), BlockT (..), BuiltinT (..), ExType (..), ExVarId (..), Ident (..), Lambda (..), NumDesc (..), Quant (..), TermT (..), Vector' (..), builtinsList, identOfBuiltin, pIdent, pQuant, pTerm, parse, recordOf, render, rowOf)
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

termLoggerM ∷ (Has Solve sig m) ⇒ m (TermT → Doc AnsiStyle)
termLoggerM = do
  ctx ← ask @(Vector Binding)
  pure $ \t → pTerm (0, (\(q, i, _, _) → (q, i)) <$> ctx) t

stackLog ∷ (Has Solve sig m) ⇒ ((TermT → Doc AnsiStyle) → Doc AnsiStyle) → m ()
stackLog f = send . StackLog . f =<< termLoggerM

stackScope ∷ (Has Solve sig m) ⇒ ((TermT → Doc AnsiStyle) → Doc AnsiStyle) → m a → m a
stackScope namef act = do
  tl ← termLoggerM
  send $ StackScope (namef tl) act

-- Monomorphised to Doc AnsiStyle.
stackError ∷ ∀ sig m a. (Has Solve sig m) ⇒ ((TermT → Doc AnsiStyle) → Doc AnsiStyle) → m a
stackError ef = do
  stackLog \_ → "<panic!!!11>"
  throwError . ef =<< termLoggerM

-- TODO: Fix the newlines
pStacks ∷ [StackEntry] → Doc AnsiStyle
pStacks = \case
  [] → mempty
  [x] → line <> "└ " <> pStack x
  (x : xs) → line <> "├ " <> pStack x <> pStacks xs

pStack ∷ StackEntry → Doc AnsiStyle
pStack = \(StackEntry x xs) → group x <> nest 2 (pStacks xs) where

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
      -- sendMsg "--"
      pure res
    R other → alg (unStackPrintC . hdl) (R other) ctx
   where
    sendMsg msg = do
      level ← ask
      sendIO $ render $ indent (level * 2) $ "├ " <> msg

runStackPrintC ∷ (Has (Lift IO) sig m) ⇒ StackPrintC m a → m a
runStackPrintC = runReader 0 . unStackPrintC

-- Check

type Solve = Reader (Vector Binding) :+: Writer Resolved :+: Fresh :+: Error (Doc AnsiStyle) :+: StackLog

writeMeta ∷ (Has Solve sig m) ⇒ Ident → ExVarId → ExType → TermT → m ()
writeMeta n var ty val = do
  stackLog \p → pIdent n <+> ":=" <+> p val
  case ty of
    ExType ty' → infer val $ Check ty'
    ExSuperType → void $ ensureIsType =<< infer val Infer
  tell $ HM.singleton var val

-- | Introduce new variable/binding.
scopedVar ∷ (Has Solve sig m) ⇒ ((TermT → m TermT) → a → m a) → (Quant, Ident, Maybe TermT, TermT) → m a → m a
scopedVar mapTerm (bindQ, bindI, bindT, bindTy) act = do
  (resolved, res) ← intercept @Resolved $ local (insertBinds (bindQ, bindI, bindT, Just bindTy)) act
  let unnest original =
        rewrite
          (const (+ 1))
          (+ 1)
          ( \term locs → case term of
              Var i | i == locs → stackError \p → "Var leaked in " <> p original
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
              UniVar _ uni2 _ | uni1 == uni2 → stackError \p → "UniVar leaked in " <> p original
              _ → pure Nothing
          )
          ()
          original
  for_ resolved ensureNotOcc
  mapTerm ensureNotOcc res

freshIdent ∷ (Has Solve sig m) ⇒ m Ident
freshIdent = (`Ident` False) . ("/" <>) . pack . show <$> fresh

scopedExVar ∷ (Has Solve sig m) ⇒ ((TermT → m TermT) → a → m a) → (Int, ExType) → m a → m a
scopedExVar mapTerm (ex1, ex1ty) act = do
  (resolved, res) ← intercept @Resolved act
  let
    -- \| Is dervative of `ex1`?
    isOfEx1 (ExVarId x) = (== ex1) $ fst $ fromMaybe (error "impossible") $ viewl x
    resolved' = HM.filterWithKey (\k _ → not $ isOfEx1 k) resolved
  -- Ensure no leak
  for_ resolved' \original →
    rewrite
      (const id)
      id
      ( \term () → case term of
          ExVar _ ex2 _
            | isOfEx1 ex2 →
                stackError \p → "ExVar leaked in " <> p original
          _ → pure Nothing
      )
      ()
      original
  tell resolved'
  -- Rewrite
  let unresolved =
        sortBy (\a b → fst a `compare` fst b)
          $ toList
          $ runIdentity
          $ execWriter @(HashMap ExVarId ExType)
          $ rewrite
            (const id)
            id
            ( \term () → case term of
                ExVar _ ex2 ty
                  | isOfEx1 ex2 → tell @(HashMap ExVarId ExType) [(ex2, ty)] $> Nothing
                _ → pure Nothing
            )
            ()
            (resolve resolved $ ExVar (Ident "" False) (ExVarId [ex1]) ex1ty)
  if null unresolved
    then pure res
    else
      mapTerm
        ( \outT →
            let rewriteExVar ex with0 =
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
                        ExSuperType → do
                          uN ← freshIdent
                          n ← freshIdent
                          pure
                            $ Pi QEra (Builtin $ Num $ NumDesc True BitsInf)
                            . Left
                            . (uN,)
                            . Lambda
                            $ Pi QEra (App (Builtin TypePlus) (Var 0))
                            . Left
                            . (n,)
                            . Lambda
                            $ rewriteExVar ex (Var 0)
                            $ nestedBy 2 acc
                        ExType ty → do
                          n ← freshIdent
                          pure $ Pi QEra ty $ Left $ (n,) $ Lambda $ rewriteExVar ex (Var 0) $ nested acc
                  )
                  outT
                  unresolved
        )
        res

withMono' ∷
  (Has Solve sig m) ⇒
  -- | Unwrap Foralls
  Bool →
  ((TermT → m TermT) → a → m a) →
  -- | onMeta
  ReaderC (Ident, ExVarId, ExType) m TermT →
  -- | onOther
  (Resolved → TermT → m a) →
  TermT →
  m a
withMono' foralls mapTerm onMeta onOther = go
 where
  go = \case
    ExVar n i ty → do
      val ← runReader (n, i, ty) onMeta
      runSeqResolve do
        withResolved \_ → writeMeta n i ty val
        withResolved \exs → onOther exs val
    Pi QEra x yE | foralls → stackScope (\_ → "(unwrapped forall)") do
      exId ← fresh
      case yE of
        Left (n, body) → scopedExVar mapTerm (exId, ExType x) $ go $ normalize [Just $ ExVar n (ExVarId [exId]) $ ExType x] $ unLambda body
        Right body → mapTerm (pure . Pi QEra x . Right) =<< go body
    r → onOther [] r

withMono ∷
  (Has Solve sig m) ⇒
  ((TermT → m TermT) → a → m a) →
  ReaderC (Ident, ExVarId, ExType) m TermT →
  (Resolved → TermT → m a) →
  TermT →
  m a
withMono = withMono' True

subExVar ∷ (Has (Reader (Ident, ExVarId, ExType) :+: Fresh) sig m) ⇒ ByteString → ExType → m TermT
subExVar subName subTy = do
  subI ← fresh
  (Ident baseName _, ExVarId baseI, _ ∷ ExType) ← ask
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
  notARow x = stackError \p → "Not a row:" <+> p x
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
            ExType (App (Builtin Row) mT) → do
              h ← subExVar "head" (ExType mT)
              t ← subExVar "tail" (ExType $ rowOf mT)
              pure $ Concat h (Right t)
            _ → do
              (n, var, _ ∷ ExType) ← ask
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
    (stackError \_ → "Unknown shape")
    ( \_ → \case
        RecordLit x → f x
        _ → stackError \_ → "Not a record"
    )
    t

ensureIsType ∷ (Has Solve sig m) ⇒ TermT → m TermT
ensureIsType t =
  withMono
    id
    (lift fails)
    ( \_ → \ty → case ty of
        App (Builtin TypePlus) _ → pure ty
        -- Currently ensureIsType is used in writeMeta for ExSuperType. So don't uncomment this without thinking!
        -- App (Builtin Row) _ → pure ty
        -- App (Builtin Record) r →
        --   rowOf <$> withKnownFields id r \fields →
        --     fromMaybe bottomRow <$> execState Nothing (unifyFields fields)
        _ → fails
    )
    t
 where
  fails = stackError \p → p t <> " is not a type?"

data InferMode a where
  Infer ∷ InferMode TermT
  Check ∷ TermT → InferMode ()

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

resolveBinds ∷ HashMap ExVarId TermT → Vector (Quant, Maybe TermT, TermT) → Vector (Quant, Maybe TermT, TermT)
resolveBinds (HM.null → True) = id
resolveBinds exs = fmap $ bimap id $ resolve exs

resolveMode ∷ HashMap ExVarId TermT → InferMode a → InferMode a
resolveMode exs = \case
  Infer → Infer
  Check a → Check $ resolve exs a

-- | Select bindings for normalizing annotations.
annoBinds ∷ (Has Solve sig m) ⇒ m (Vector (Maybe TermT))
annoBinds = (fmap \(_, _, a, _) → a) <$> ask @(Vector Binding)

-- | Select bindings for normalizing terms.
termBinds ∷ (Has Solve sig m) ⇒ m (Vector (Maybe TermT))
termBinds =
  let f = \(q, _, a, _) → case q of
        QEra → Just undefined -- Just and not Nothing to make sure `normalize` erases it.
        QNorm → a
   in (fmap f) <$> ask @(Vector Binding)

checkDepLam ∷ ∀ sig m. (Has Solve sig m) ⇒ Quant → Ident → Lambda TermT → TermT → Lambda TermT → m ()
checkDepLam q i bod inT outT =
  scopedVar (const pure) (q, i, Nothing, inT)
    $ infer (unLambda bod)
    $ Check
    $ normalize [Just $ Var 0]
    $ unLambda outT

checkLam ∷ ∀ sig m. (Has Solve sig m) ⇒ Quant → Ident → Lambda TermT → TermT → Either (Ident, Lambda TermT) TermT → m ()
checkLam q i bod inT outT = case outT of
  Left (_, outT') → checkDepLam q i bod inT outT'
  Right outT' → scopedVar (const pure) (q, i, Nothing, inT) $ infer (unLambda bod) $ Check $ nested outT'

inferApp ∷ (Has Solve sig m) ⇒ Quant → TermT → TermT → m TermT
inferApp q f a = runSeqResolve do
  let norm = q == QNorm
  fTy ← withResolved \_ → infer f Infer
  withResolved \_ →
    withMono'
      norm
      id
      ( if norm
          then Pi QNorm <$> subExVar "in" ExSuperType <*> (Right <$> subExVar "out" ExSuperType)
          else stackError \_ → "Cannot apply erased argument to unknown"
      )
      ( \_ → \case
          Pi q2 inT outTE | q == q2 → runSeqResolve do
            let updCtx = if norm then id else local @(Vector Binding) ((\(_, i, t, ty) → (QNorm, i, t, ty)) <$>)
            withResolved \_ → updCtx $ infer a $ Check $ inT
            withResolved \exs3 → case outTE of
              Left (_, outT) → do
                ab ← annoBinds
                pure $ resolve exs3 $ normalize [Just $ normalize ab a] $ unLambda outT
              Right outT → pure $ resolve exs3 outT
          t → stackError \p → "inferApp" <+> pretty (show q) <+> p t
      )
      fTy

-- stackScope ("<" <> group (pTerm' t) <> "> : " <> pMode mode) $
logAndRunInfer ∷ ∀ sig m a. (Has Solve sig m) ⇒ ((TermT, InferMode a) → m a) → TermT → InferMode a → m a
logAndRunInfer f t mode =
  let
    scope x = stackScope @sig @m @a \p → ("<" <> group (p t) <> "> : " <> x p)
    act = f (t, mode)
   in
    case mode of
      Infer → scope (\_ → "_") do
        res ← act
        when (t /= BuiltinsVar) $ stackLog \p → p res
        pure res
      Check t' → scope (\p → p t') act

numFitsInto ∷ Integer → NumDesc → Bool
numFitsInto x d =
  numDecDispatch
    d
    (\(_ ∷ Proxy e) → fromIntegral (minBound @e) <= x && fromIntegral (maxBound @e) >= x)
    (\_ → True)

-- | Either infers a normalized type for the value and context, or checks a value against the normalized type.
infer ∷ ∀ sig m a. (Has Solve sig m) ⇒ TermT → InferMode a → m a
infer = logAndRunInfer \case
  -- Here, we will convert Checks to Infers.
  -- However, converting Infer to a Check when checking a term is hereby declared a deadly sin.
  (Block (BlockLet q name tyM val into), mode) → runSeqResolve do
    ty ← withResolved \_ → stackScope (\_ → ("let" <+> pQuant q <> pIdent name)) case tyM of
      Nothing → infer val Infer
      Just ty → do
        ab ← annoBinds
        -- TODO: check ty' to be a type?
        -- EDIT: typechecking is undecidable... so... uh... no?
        let ty' = normalize ab ty
        infer val $ Check ty'
        pure ty'
    val' ← withResolved \_ → do
      tb ← termBinds
      pure $ normalize tb val
    let withLog act = case (unLambda into) of
          Block{} → act
          _ → stackScope (\_ → "in") act
    withResolved \exs →
      withLog
        $ scopedVar (mapTermFor mode) (q, name, Just val', ty)
        $ infer (unLambda into)
        $ nestMode
        $ resolveMode exs mode
  -- TODO: (Lam QEra arg bod, Infer)
  (Lam QEra n bod, Check (Pi QEra inT outT)) → checkLam QEra n bod inT outT
  (AppErased f a, Infer) → inferApp QEra f a
  (term, Check (Pi QEra xTy (Left (n, yT)))) → do
    uniId ← fresh
    scopedUniVar (const pure) uniId $ infer term $ Check $ normalize [Just $ UniVar n uniId xTy] $ unLambda yT
  (term, Check (Pi QEra _ (Right yT))) → infer term $ Check yT
  (Lam QNorm n bod, Infer) → do
    inT ← fresh
    let inT' = ExVar n (ExVarId [inT]) ExSuperType
    scopedExVar id (inT, ExSuperType) $ runSeqResolve do
      outT ← withResolved \_ →
        scopedVar id (QNorm, n, Nothing, inT') $ infer (unLambda bod) Infer
      withResolved \exs → pure $ Pi QNorm (resolve exs inT') $ Right outT
  (Lam QNorm n bod, Check (Pi QNorm inT outT)) → checkLam QNorm n bod inT outT
  (App (App (Builtin RecordGet) tag) record, mode) → runSeqResolve do
    recordT ← withResolved \_ → infer record Infer
    withResolved \_ → infer tag $ Check $ Builtin Tag
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
            _ → stackError \_ → "App RecordGet"
       in
        withMono
          (mapTermFor mode)
          ( do
              tVar ← subExVar "t" ExSuperType
              rowVar ← subExVar "row" $ ExType $ rowOf tVar
              pure $ recordOf rowVar
          )
          ( \exs2 → \case
              App (Builtin Record) row → body row exs2
              _ → stackError \_ → "Not a record"
          )
          (resolve exs recordT)
  (App f a, Infer) → inferApp QNorm f a
  (RecordLit flds, Infer) → runSeqResolve do
    rowFields ← for flds \(n, v) → do
      withResolved \_ → infer n $ Check $ Builtin Tag
      vTy ← withResolved \_ → infer v Infer
      pure (n, vTy)
    pure $ recordOf $ RecordLit rowFields
  (ListLit (Vector' values), Infer) →
    let
      rec unifiedTy0M =
        viewl >>> \case
          Nothing → pure unifiedTy0M
          Just (v, vs) → do
            runSeqResolve do
              unifiedTy ← withResolved \_ → case unifiedTy0M of
                Nothing → infer v Infer
                Just unifiedTy0 → runSeqResolve do
                  withResolved \_ → infer v (Check unifiedTy0)
                  withResolved \exs → pure (resolve exs unifiedTy0)
              withResolved \_ → rec (Just unifiedTy) vs
     in
      App (Builtin List) . fromMaybe (Builtin Never) <$> rec Nothing values
  (Concat l rE, Infer) →
    let
      -- TODO: what should be here?
      withKnown t f = withMono id (stackError \_ → "TODO Concat infer") (\_exs → f) t
      withKnownFields' = withKnownFields id
      concatT lT rT = case (lT, rT, rE) of
        (App (Builtin Record) lR, App (Builtin Record) rR, Right _) → pure $ recordOf $ concat lR rR
        (App (Builtin Record) lR, App (Builtin Record) rR, Left (_, Lambda _)) →
          rowOf <$> withKnownFields' lR \lR' → withKnownFields' rR \rR' →
            fromMaybe (Builtin Never)
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
        _ → stackError \_ → "Concat of non-records"
     in
      runSeqResolve do
        lT ← withResolved \_ → infer l Infer
        rT ← withResolved \_ →
          either
            ( \(n, r) → do
                ab ← annoBinds
                scopedVar id (QNorm, n, Nothing, recordOf $ normalize ab l)
                  $ infer
                    (unLambda r)
                    Infer
            )
            (\r → infer r Infer)
            rE
        withResolved \exs →
          withKnown (resolve exs lT) \lT' → withKnown rT \rT' → concatT lT' rT'
  (NumLit x, Check (Builtin (Num d))) →
    if x `numFitsInto` d
      then pure ()
      else stackError \_ → "Number literal " <> pretty x <> " does not fit into " <> pIdent (identOfBuiltin $ Num d)
  (NumLit x, Infer) →
    pure
      $ Builtin
      $ Num
      $ let candidates = NumDesc False <$> [Bits8, Bits16, Bits32, Bits64]
         in fromMaybe (NumDesc False BitsInf) $ find @[] (x `numFitsInto`) candidates
  (TagLit _, Infer) → pure $ Builtin Tag
  (BoolLit _, Infer) → pure $ Builtin Bool
  (Var i, Infer) → do
    binds ← ask @(Vector Binding)
    case binds !? i of
      Just (QNorm, _, _, Just ty) → do
        stackLog \p → "var" <+> pretty i <+> ":" <+> p ty
        pure ty
      _ → stackError \_ → "Unknown var #" <> pretty i
  -- TODO: Support checks...
  -- (Quantification _ _name kind ty, Infer) → do
  --   res ← scopedVar id $ infer (insertBinds (QNorm, Nothing, normalize (annoBinds binds) kind) binds) (unLambda ty) Infer
  --   ensureIsType res
  -- (Pi inNameM x y, Check (App (Builtin Type) u)) → do
  --   infer x $ Check $ typOf u
  --   (if isJust inNameM then local @BindsT (|> (Nothing, PortableTerm valNesting0 x)) else id)
  --     $ infer y
  --     $ Check
  --     $ typOf u
  (Pi _q inTy (Right outTy), Infer) → runSeqResolve do
    inTyTy ← withResolved \_ → ensureIsType =<< infer inTy Infer
    withResolved \_ →
      -- TODO: recheck
      withMono
        id
        (stackError \_ → "impossible")
        ( \_ inTyTy' → runSeqResolve do
            withResolved \_ → infer outTy $ Check inTyTy'
            withResolved \exs2 → pure $ resolve exs2 inTyTy'
        )
        inTyTy
  (Builtin x, Infer) → pure $ typOfBuiltin x
  (BuiltinsVar, Infer) →
    pure
      $ App (Builtin Record)
      $ RecordLit
      $ Vector'
      $ (\b → (TagLit $ identOfBuiltin b, typOfBuiltin b))
      <$> builtinsList
  (UniVar _n _i ty, Infer) → pure ty
  (ExVar _n _i (ExType ty), Infer) → pure ty
  (Sorry, Check k) → stackLog \p → "sorry :" <+> p k
  (k, Infer) → stackError \p → p k
  (term, Check c) → stackScope (\p → "check via infer" <+> p term <+> ":" <+> p c) $ runSeqResolve do
    ty ← withResolved \_ → infer term Infer
    withResolved \exs → subtype (resolve exs ty) $ resolve exs c

typOfBuiltin ∷ BuiltinT → TermT
typOfBuiltin =
  \case
    Num _d → [termQQ| Type+ 0 |]
    Add d → opd d
    Sub d → opd d
    Tag → [termQQ| Type+ 0 |]
    Bool → [termQQ| Type+ 0 |]
    Row → [termQQ| u : Int+ -@> Type+ u -> Type+ u |]
    Record → [termQQ| u : Int+ -@> Row (Type+ u) -> Type+ u |]
    List → [termQQ| u : Int+ -@> Type+ u -> Type+ u |]
    TypePlus → [termQQ| u : Int+ -> Type+ (u + 1) |]
    Eq → [termQQ| u : Int+ -@> a : Type+ u -@> a -> a -> Type+ u |]
    Refl → [termQQ| u : Int+ -@> a : Type+ u -@> x : a -@> Eq x x |]
    RecordGet →
      [termQQ|
        u : Int+ -@> row : Row (Type+ u) -@> t : Type+ u -@>
          tag : Tag ->
          record : Record ({(tag) = t} \/ row) ->
          t
      |]
    -- TODO: Better type
    RecordKeepFields → [termQQ| u : Int+ -@> row : Row (Type+ u) -@> List Tag -> Record row -> Record row |]
    RecordDropFields → [termQQ| u : Int+ -@> row : Row (Type+ u) -@> List Tag -> Record row -> Record row |]
    ListLength → [termQQ| u : Int+ -@> A : Type+ u -@> List A -> Int+ |]
    ListIndexL → [termQQ| u : Int+ -@> A : Type+ u -@> i : Int+ -> l : List A -> Where (i < list_length l) -@> A |]
    NatFold → [termQQ| u : Int+ -@> Acc : (Int+ -> Type+ u) -@> Acc 0 -> (i : Int+ -> Acc i -> Acc (i + 1)) -> n : Int+ -> Acc n |]
    If → [termQQ| u : Int+ -@> A : Type+ u -@> cond : Bool -> (Eq cond true -> A) -> (Eq cond false -> A) -> A |]
    ULte → [termQQ| Int -> Int -> Bool |]
    ULt → [termQQ| Int -> Int -> Bool |]
    UEq → [termQQ| Int -> Int -> Bool |]
    UNeq → [termQQ| Int -> Int -> Bool |]
    W → [termQQ| u : Int+ -@> Type+ u -> Type+ u |]
    Wrap → [termQQ| u : Int+ -@> A : Type+ u -@> A -> W A |]
    Unwrap → [termQQ| u : Int+ -@> A : Type+ u -@> W A -> A |]
    Never → [termQQ| Type+ 0 |]
 where
  opd d = Pi QNorm (Builtin $ Num d) $ Right $ Pi QNorm (Builtin $ Num d) $ Right $ Builtin $ Num d

instMeta ∷ ∀ sig m. (Has Solve sig m) ⇒ Ident → ExVarId → ExType → TermT → m ()
instMeta = (\f a b c d → stackScope (\_ → "instMeta") $ f a b c d) \n1 (ExVarId var1) t1 →
  let instMeta' ∷ TermT → m TermT
      instMeta' = \case
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
        App (Builtin W) a → pure $ Builtin W `App` a
        App f a → runSeqResolve do
          f' ← withResolved \_ → instMeta' f
          a' ← withResolved \exs → instMeta' $ resolve exs a
          pure $ App f' a'
        RecordLit flds → RecordLit <$> traverse (bitraverse instMeta' instMeta') flds
        Concat a b → runSeqResolve do
          a' ← withResolved \_ → instMeta' a
          b' ← withResolved \exs →
            either
              (\(n, b'') → fmap (Left . (n,) . Lambda) $ scopedVar id (QNorm, n, Nothing, a') $ instMeta' $ resolve' 1 exs $ unLambda b'')
              (fmap Right . instMeta' . resolve exs)
              b
          pure $ Concat a' b'
        Var x → pure $ Var x -- TODO: I hope this is correct, but needs to be rechecked.
        Builtin x → pure $ Builtin x
        NumLit x → pure $ NumLit x
        Pi QNorm inT outT → runSeqResolve do
          inT' ← withResolved \_ → instMeta' inT
          outT' ←
            withResolved
              ( \exs →
                  either
                    (\(n, v) → fmap (Left . (n,) . Lambda) $ scopedVar id (QNorm, n, Nothing, inT') $ instMeta' (resolve' 1 exs $ unLambda v))
                    (fmap Right . instMeta' . resolve exs)
                    outT
              )
          pure $ Pi QNorm inT' outT'
        x → stackError \p → "instMeta (of" <+> pretty (tshow $ ExVarId var1) <> ")" <+> p x
   in \val →
        let r = writeMeta n1 (ExVarId var1) t1 =<< instMeta' val
         in case val of
              ExVar _ var2 _ →
                if var2 == ExVarId var1
                  then pure ()
                  else r
              _ → r

-- TODO: Use isEq.

-- | a <: b Check if type `a` is a subtype of type `b`.
subtype ∷ ∀ sig m. (Has Solve sig m) ⇒ TermT → TermT → m ()
subtype = \a b →
  stackScope (\p → p a <+> annotate (color Cyan) "<:" <+> p b) $ subtype' a b
 where
  -- Core subtyping logic based on the structure of the resolved types.
  subtype' ∷ TermT → TermT → m ()
  subtype' = curry \case
    -- Existential Variables (?a <: ?b, ?a <: T, T <: ?a)
    (ExVar _ ex1 _, ExVar _ ex2 _) | ex1 == ex2 → pure ()
    (ExVar n1 ex1 ty1, t2) → instMeta n1 ex1 ty1 t2
    (t1, ExVar n2 ex2 ty2) → instMeta n2 ex2 ty2 t1
    -- Universal Variables (u1 <: u2) - Must be identical.
    (UniVar _ id1 _, UniVar _ id2 _) | id1 == id2 → pure ()
    -- T <: Pi QEra x:K. Body  => Introduce UniVar for x
    (t, Pi QEra k (Left (n, body))) → do
      uniId ← fresh
      scopedUniVar (const pure) uniId
        $ subtype t
        $ normalize [Just $ UniVar n uniId k]
        $ unLambda body
    -- Pi QEra x:K. Body <: T => Introduce ExVar for x
    (Pi QEra k (Left (n, body)), t) → do
      exId ← fresh
      scopedExVar (\_ _ → stackError \_ → "Unresolved existential" <+> pIdent n) (exId, ExType k)
        $ subtype (normalize [Just $ ExVar n (ExVarId [exId]) $ ExType k] $ unLambda body) t

    -- Function Types (Πx:T1.U1 <: Πy:T2.U2)
    (Pi q1 inT1 outT1E, Pi q2 inT2 outT2E) | q1 == q2 → runSeqResolve do
      -- Input types are contravariant (T2 <: T1)
      withResolved \_ → subtype inT2 inT1
      -- Output types are covariant
      withResolved \exs →
        let process name bod1 bod2 = do
              uniId ← fresh
              scopedUniVar (const pure) uniId do
                let var = UniVar name uniId inT2 -- Use common name/type for substitution
                let body1 = resolve exs $ either id (normalize [Just var] . unLambda) bod1
                let body2 = resolve exs $ either id (normalize [Just var] . unLambda) bod2
                subtype body1 body2
         in case (outT1E, outT2E) of
              -- Both non-dependent
              (Right outT1, Right outT2) → subtype (resolve exs outT1) (resolve exs outT2)
              (Left (_n1, lbd1), Left (n2, lbd2)) → process n2 (Right lbd1) (Right lbd2)
              (Left (n1, lbd1), Right outT2) → process n1 (Right lbd1) (Left outT2)
              (Right outT1, Left (n2, lbd2)) → process n2 (Left outT1) (Right lbd2)
    (Builtin (Num d1@(NumDesc nonneg1 bits1)), Builtin (Num d2@(NumDesc nonneg2 bits2))) →
      let fits = case (nonneg1, nonneg2) of
            (True, False) → bits1 < bits2 || bits2 == BitsInf
            (False, True) → False
            _ → bits1 <= bits2
       in if fits then pure () else stackError \_ → "Cannot fit " <> pIdent (identOfBuiltin $ Num d1) <> " into " <> pIdent (identOfBuiltin $ Num d2)
    (Builtin Never, _) → pure ()
    -- Builtin Types (must be identical)
    (Builtin a, Builtin b) | a == b → pure ()
    (Var i, Var j) | i == j → pure ()
    -- Type Universes (Type L1 <: Type L2 where L1 <= L2)
    (App (Builtin TypePlus) a, App (Builtin TypePlus) b) → do
      case (a, b) of
        (NumLit x, NumLit y) | x <= y → pure ()
        (NumLit 0, _) → pure ()
        -- If one level is existential, unify it with the other level constraint.
        (ExVar nA exA tyA, lvl2) → instMeta nA exA tyA lvl2
        (lvl1, ExVar nB exB tyB) → instMeta nB exB tyB lvl1
        _ → runSeqResolve do
          r ← withResolved \_ → isEqUnify a b
          case r of
            EqYes → pure ()
            _ → withResolved \exs → stackError \p → "Cannot subtype universes with levels:" <+> p (resolve exs a) <+> "<=" <+> p (resolve exs b)
    (App (Builtin List) a, App (Builtin List) b) → subtype a b
    -- Record/Row types (requires structural subtyping logic)
    (App (Builtin Record) row1, App (Builtin Record) row2) → subtype row1 row2 -- Delegate to row subtyping
    (App (Builtin Row) fields1, App (Builtin Row) fields2) → subtype fields1 fields2
    (App (Builtin Record) fieldsVal, App (Builtin Row) fieldsTy) →
      withKnownFields (\_ _ → stackError \_ → "Unresolved existentials") fieldsVal \fi →
        runState (\_ _ → pure ()) (Just fieldsTy) $ unifyFields fi
    (App (Builtin W) a, App (Builtin W) b) →
      isEqUnify a b >>= \case
        EqYes → pure ()
        _ → stackError \p → "Cannot equate wrapped types" <+> p a <+> "and" <+> p b
    -- App f1 a1 <: App f2 a2
    (App f1 a1, App f2 a2) → runSeqResolve do
      eqF ← withResolved \_ → isEqUnify f1 f2
      case eqF of
        EqYes → do
          eqA ← withResolved \exs → isEqUnify (resolve exs a1) (resolve exs a2)
          case eqA of
            EqYes → pure ()
            _ → stackError \p → "Cannot subtype applications with different arguments:" <+> p a1 <+> "vs" <+> p a2
        _ → stackError \p → "Cannot subtype applications with different functions:" <+> p f1 <+> "vs" <+> p f2
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
                    EqUnknown → stackError \_ → "Unable to check field equality when subtyping"
                    EqNot → rec
              )
              (stackError \_ → "Missing field from left side when subtyping")
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

    -- Catch-all: if no rule matches, they are not subtypes
    (t1, t2) → stackError \p → "Subtype check failed, no rule applies for:" <+> p t1 <+> "<:" <+> p t2

runSolveM ∷ (Applicative m) ⇒ ReaderC (Vector Binding) (WriterC Resolved (FreshC (ErrorC (Doc AnsiStyle) m))) a → m (Either (Doc AnsiStyle) a)
runSolveM =
  runError (pure . Left) (pure . Right)
    . evalFresh 0
    . runWriter (const pure) -- TODO: alert on unhandled?
    . runReader []

checkSource ∷ ByteString → IO ()
checkSource source = do
  term ← either (fail . show) pure $ parse [] source
  (stacks, res) ← runStackAccC $ runSolveM $ infer term Infer
  render case res of
    Left e →
      pStacks stacks
        <> line
        <> annotate (color Red) "error: "
        <> e
    Right r → pTerm (0, []) r

checkSourceDebug ∷ ByteString → IO ()
checkSourceDebug source = do
  term ← either (fail . show) pure $ parse [] source
  res ← runStackPrintC $ runSolveM $ infer term Infer
  render case res of
    Left e → annotate (color Red) "error: " <> e
    Right r → pTerm (0, []) r

checkFile ∷ FilePath → IO ()
checkFile file = checkSource =<< readFileBinary file

checkFileDebug ∷ FilePath → IO ()
checkFileDebug file = checkSourceDebug =<< readFileBinary file

main ∷ IO ()
main = pure ()
