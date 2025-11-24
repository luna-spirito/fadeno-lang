{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use const" #-}

module Main (main, parseFile, formatFile, formatModule, loadModule, normalizeModule, checkModule, checkModuleDebug, compileModule, decompileModule, build, watch) where

import Compiler (compileModule, decompileModule)
import Control.Algebra
import Control.Carrier.Error.Church (ErrorC, runError)
import Control.Carrier.Fresh.Church (FreshC, evalFresh)
import Control.Carrier.Reader (ReaderC, runReader)
import Control.Carrier.State.Church (State, StateC, evalState)
import Control.Carrier.Writer.Church (WriterC, runWriter)
import Control.Effect.Error (throwError)
import Control.Effect.Fresh (Fresh, fresh)
import Control.Effect.Lift (Lift, sendIO)
import Control.Effect.Reader (Reader, ask, local)
import Control.Effect.State (get, modify, put)
import Control.Effect.Throw (Throw)
import Control.Effect.Writer (Writer, censor, tell)
import Data.Bitraversable (bimapM)
import Data.Foldable (foldlM)
import Data.List (find)
import Data.RRBVector (Vector, adjust, adjust', deleteAt, findIndexL, ifoldr, replicate, splitAt, take, viewl, viewr, zip, (!?), (<|), (|>))
import GHC.Exts (IsList (..))
import NameGen
import Normalize (Context, Dyn (..), EEntry (..), Epoch (..), EqRes (..), Imports (..), Rewrite (..), Scopes (..), applyLambda, applyLambdaRefineGetSkip, dyn, fDyn, fetchLambda, fetchT, getEpoch, getScopeId, isEq', normalize, normalize', normalizeModule, numDecDispatch, runSubContext, termQQ, withBinding, withMarked)
import Parser (Bits (..), BlockF (..), BuiltinT (..), FieldsK (..), Ident (..), IsErased (..), Lambda (..), Module (..), NumDesc (..), Quant (..), RefineK (..), Term (..), TermF (..), Vector' (..), builtinsList, dotvar, formatFile, formatModule, freshIdent, identOfBuiltin, loadModule, loadModule', maxOf, nested, nestedBy', nestedByP, pIdent, pQuant, pTerm, parseFile, render, rowOf, splitAt3, traverseTermF, typ, typOf, pattern TApp, pattern TBuiltin)
import Prettyprinter (Doc, annotate, group, indent, line, list, nest, pretty, (<+>))
import Prettyprinter.Render.Terminal (AnsiStyle, Color (..), color)
import RIO hiding (Reader, Vector, ask, concat, drop, filter, link, local, replicate, runReader, take, to, toList, zip)
import RIO.Time (UTCTime)
import Ser (serializeCompileResult)
import System.Directory.OsPath (getModificationTime)
import System.File.OsPath (writeFile')
import System.IO (print)
import System.OsPath (OsPath, encodeUtf, replaceExtension, unsafeEncodeUtf)
import System.Environment (getArgs)

-- TODO: Permit inference of dependent Pis?
-- TODO: Concat uncomfortably replicates Pi.
-- TODO: There are few deadly sins (Infer → Check conversions) that should be removed. Infer should never invoke check! (Pi/inferList/???)
-- TODO: `3 \/ 4` shouldn't probably typecheck.
-- TODO: I've earlier declared converting Infers to Checks a sin. However, I'm starting to believe that, instead, converting Checks to Infers is sin and
-- must be avoided at all costs.
-- TODO: Currently, we do not check if type signatures are sensible. So we could write:
-- ```fad
-- /: Fun (u) -> Type^ u
-- test = \_. Int
--
-- in test (-1)
-- ```

type Checker = Context :+: Fresh :+: State UsedNames :+: StackLog :+: Throw (Doc AnsiStyle)

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

termLoggerM ∷ (Has Context sig m) ⇒ m (Term → Doc AnsiStyle)
termLoggerM = (\(Scopes ctx _ _) → pTerm $ (\(_, n, t, _) → (n, t >>= asBuiltin)) <$> ctx) <$> get @Scopes
 where
  asBuiltin = \case
    Term (Builtin x) → Just x
    _ → Nothing

stackLog ∷ (Has (Context :+: StackLog) sig m) ⇒ ((Term → Doc AnsiStyle) → Doc AnsiStyle) → m ()
stackLog f = send . StackLog . f =<< termLoggerM

stackScope ∷ (Has (Context :+: StackLog) sig m) ⇒ ((Term → Doc AnsiStyle) → Doc AnsiStyle) → m a → m a
stackScope namef act = do
  tl ← termLoggerM
  send $ StackScope (namef tl) act

-- Monomorphised to Doc AnsiStyle.
stackError ∷ ∀ sig m a. (Has Checker sig m) ⇒ ((Term → Doc AnsiStyle) → Doc AnsiStyle) → m a
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
pStack (StackEntry x xs) = group x <> nest 2 (pStacks xs)

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
      local @Int (+ 1) $ unStackPrintC $ hdl (ctx $> act)
    R other → alg (unStackPrintC . hdl) (R other) ctx
   where
    sendMsg msg = do
      level ← ask
      sendIO $ render $ indent (level * 2) $ "├ " <> msg

runStackPrintC ∷ (Has (Lift IO) sig m) ⇒ StackPrintC m a → m a
runStackPrintC = runReader 0 . unStackPrintC

-- Check

writeMeta ∷ ∀ sig m. (Has Checker sig m) ⇒ (Int, Int) → (Int, Term) → m ()
writeMeta exId0@(scope0, subi0) (valLocals0, valNow0) = do
  stackLog \p → "exi# " <> pretty exId0 <+> ":=" <+> p valNow0
  depth ← (\scope → scope - scope0) <$> getScopeId -- no -1 due to scope being ridiculous
  val0 ← maybe (stackError \_ → "Leak") pure $ nestedBy' valLocals0 valNow0 $ -depth
  Scopes (splitAt scope0 → (bindsBefore, bindsAfter)) (splitAt3 scope0 → (exsBefore, exsMiddleM, exsAfter)) rs0 ← get @Scopes
  (Epoch exsMiddleEpoch, (exsMiddleBef, exsMiddleMiddle, exsMiddleAft)) ← maybe (stackError \_ → "ex not found in context") pure do
    middle ← exsMiddleM
    i ←
      findIndexL
        ( \case
            EVar subi2 _ → subi2 == subi0
            _ → False
        )
        $ snd middle
    pure $ splitAt3 i <$> middle
  let
    rewrites =
      foldl'
        ( \acc → \case
            ERewrite{} → acc + 1
            _ → acc
        )
        0
        (exsMiddleAft <> (snd =<< exsAfter))
    rsBef = take (length rs0 - rewrites) rs0
  put $ Scopes bindsBefore (exsBefore |> (Epoch exsMiddleEpoch, exsMiddleBef)) rsBef
  case exsMiddleMiddle of
    Just (EVar _ (Right ty)) → infer val0 $ Check ty
    _ → stackError \_ → "Internal error: existential already instantiated"
  modify @Scopes \(Scopes bs es _) → Scopes bs (adjust' scope0 (bimap (\(Epoch i) → Epoch $ i + 1) (|> EVar subi0 (Left (valLocals0, val0)))) es) rsBef
  let
    fe ∷ EEntry → m ()
    fe e0 = do
      (e1, rsf) ← case e0 of
        EMarker → pure (EMarker, id)
        EVar exId valty → do
          valty' ← bimapM (traverse normalize) normalize valty
          pure (EVar exId valty', id)
        EUniVar n → pure (EUniVar n, id)
        ERewrite (Rewrite locsCount lfromto0) → do
          let locs = replicate locsCount Nothing
          lfromto ← fmap Lambda $ bimapM (normalize' locs) (normalize' locs) $ unLambda lfromto0
          s ← getScopeId
          let rewr = Rewrite locsCount lfromto
          pure (ERewrite rewr, (|> (s, rewr)))
      modify @Scopes \(Scopes bs es rs) → Scopes bs (adjust (length es - 1) (fmap (|> e1)) es) $ rsf rs
  for_ exsMiddleAft fe
  when (length bindsAfter /= length exsAfter) $ error "Binds/exs mismatch"
  for_ (zip bindsAfter exsAfter) \((q, n, val, ty), (Epoch epoch, e)) → do
    ty' ← normalize ty
    modify @Scopes \(Scopes bs es rs) → Scopes (bs |> (q, n, val, ty')) (es |> (Epoch $ epoch + 1, [])) rs
    for_ e fe

-- -- TODO: Dependent.

-- | Introduce new variable/binding.
scopedVar ∷ (Has Checker sig m) ⇒ ((Term → m Term) → a → m a) → (Quant, Maybe Ident, Maybe Term, Term) → m a → m a
scopedVar mapTerm (bindQ, bindI, bindT, bindTy) act = do
  outT ← withBinding (bindQ, bindI, bindT, bindTy) act
  mapTerm (\t → maybe (stackError \p → "Var leaked in" <+> p t) pure $ nestedBy' 0 t $ -1) outT

scopedUniVar ∷ (Has Checker sig m) ⇒ ((Term → m Term) → a → m a) → Term → (Term → m a) → m a
scopedUniVar mapTerm ty act = do
  scope1 ← getScopeId
  sub1 ← fresh
  modify @Scopes \(Scopes bs es rs) → Scopes bs (adjust' scope1 (fmap (<> [EUniVar sub1])) es) rs
  let ensureNotOcc = fix \rec →
        unTerm >>> fmap Term . \case
          UniVar uni2 _ | (scope1, sub1) == uni2 → stackError \_ → "UniVar leaked"
          x → traverseTermF rec (fmap Lambda . rec . unLambda) x
  res ← act (Term $ UniVar (scope1, sub1) ty) >>= mapTerm ensureNotOcc
  modify @Scopes \(Scopes bs es rs) → Scopes bs (adjust' scope1 (fmap $ maybe (error "impossible") fst . viewr) es) rs
  pure res

-- TODO: Why scopedExVar doesn't Dyn?
scopedExVar ∷ (Has Checker sig m) ⇒ ((Term → m Term) → a → m a) → Term → (Term → m a) → m a
scopedExVar mapTerm ty0 act = do
  scopeId ← getScopeId
  sub ← fresh
  (finalEntries, res) ← withMarked [EVar sub (Right ty0)] $ act $ Term $ ExVar (scopeId, sub)
  let unresolved =
        foldl'
          ( \acc e → case e of
              EVar _ (Left _) → acc
              EVar i (Right ty) → acc |> (i, ty)
              _ → error "Unexpected entry"
          )
          []
          finalEntries
  -- TODO: occurence check?
  if null unresolved
    then pure res
    else
      mapTerm
        ( \t →
            -- \| binds is `Vector (ExVarId, Term)`
            let resolve binds =
                  run
                    . runReader @Int 0
                    . fix
                      ( \rec →
                          unTerm >>> fmap Term . \case
                            Var n → do
                              locs ← ask @Int
                              pure
                                $ if n >= locs
                                  then Var $ n + length binds
                                  else Var n
                            ExVar (scopeId2, j)
                              | scopeId == scopeId2
                              , Just indL ← findIndexL ((== j) . fst) binds → do
                                  locs ← ask
                                  pure $ Var $ locs + (length binds - indL - 1)
                            x → traverseTermF rec (fmap Lambda . local @Int (+ 1) . rec . unLambda) x
                      )
             in foldr
                  ( \(newBindId, newBindTy0) rec binds → do
                      n ← freshIdent
                      let newBindTy = resolve binds newBindTy0
                      Term . Pi QEra (Just n) newBindTy . Lambda <$> rec (binds |> (newBindId, newBindTy))
                  )
                  (\binds → pure $ resolve binds t)
                  unresolved
                  []
        )
        res

writeExBefore ∷ (Has Checker sig m) ⇒ Vector (Int, Term) → (Int, Int) → m ()
writeExBefore entries (scopeI, beforeSub) = do
  stackLog \p → list ((\(u, t) → pretty u <+> ":" <+> p t) <$> toList entries) <+> "<| (" <> pretty scopeI <> ", " <> pretty beforeSub <> ")"
  modify @Scopes \(Scopes bs exs rs) →
    Scopes
      bs
      ( adjust'
          scopeI
          ( fmap \scope →
              let (before, after) =
                    splitAt
                      ( fromMaybe (error "Ex not found in context")
                          $ findIndexL
                            ( \case
                                EVar sub _ → beforeSub == sub
                                _ → False
                            )
                            scope
                      )
                      scope
               in before <> fmap (\(i, t) → EVar i $ Right t) entries <> after
          )
          exs
      )
      rs

subExVar ∷ (Has (Reader Int :+: Writer (Vector (Int, Term)) :+: Fresh) sig m) ⇒ Term → m Term
subExVar ty = do
  scope ← ask
  sub ← fresh
  tell @(Vector (Int, Term)) [(sub, ty)]
  pure $ Term $ ExVar (scope, sub)

withMono' ∷
  (Has Checker sig m) ⇒
  -- | Unwrap Pis?, unwrap Refine?
  (Bool, Bool) →
  ((Term → m Term) → a → m a) →
  -- | onMeta
  ReaderC Int (WriterC (Vector (Int, Term)) m) Term →
  -- | onOther
  (Term → m a) →
  Term →
  m a
withMono' (pis, refines) mapTerm onMeta onOther = go
 where
  go =
    unTerm >>> \case
      ExVar (scope, sub) → do
        (newExs, res) ← runWriter (curry pure) $ runReader scope onMeta
        writeExBefore newExs (scope, sub)
        writeMeta (scope, sub) (0, res)
        onOther res
      Pi QEra _n x y
        | pis →
            stackScope (\_ → "(unwrapped forall)")
              $ scopedExVar
                mapTerm
                x
                (go <=< applyLambda y)
      Refine (RefinePreTy _ ann base)
        | refines →
            stackScope (\_ → "(unwrapped @|...|)")
              $ scopedUniVar
                mapTerm
                ann
                (go <=< applyLambda base)
      Refine (RefinePostTy base _ _) | refines → go base
      r → onOther $ Term r

withMono ∷
  (Has Checker sig m) ⇒
  ((Term → m Term) → a → m a) →
  ReaderC Int (WriterC (Vector (Int, Term)) m) Term →
  (Term → m a) →
  Term →
  m a
withMono = withMono' (True, True)

withRewr ∷ (Has Checker sig m) ⇒ Rewrite → m a → m a
withRewr rewr cont = do
  i ← getScopeId
  modify \(Scopes bs es rs) → Scopes bs (adjust' i (fmap (|> ERewrite rewr)) es) (rs |> (i, rewr))
  cont <* modify \(Scopes bs es rs) →
    Scopes
      bs
      (adjust' i (fmap $ maybe (error "Scope disappeared") fst . viewr) es)
      (maybe (error "Rewrite disappeared") fst $ viewr rs)

data InferMode a where
  Infer ∷ InferMode Term
  Check ∷ Term → InferMode ()

mapTermFor ∷ (Applicative m) ⇒ InferMode a → ((Term → m Term) → a → m a)
mapTermFor = \case
  Infer → id
  Check _ → const pure

logAndRunInfer ∷ ∀ sig m a. (Has Checker sig m) ⇒ ((TermF Term, (Epoch, InferMode a)) → m a) → Term → InferMode a → m a
logAndRunInfer f t mode =
  let act = getEpoch >>= \e → f (unTerm t, (e, mode))
   in case t of
        Term Block{} → act -- No logging to reduce noise
        _ →
          let
            scope x = stackScope @sig @m @a \p → "<" <> group (p t) <> "> : " <> x p
           in
            case mode of
              Infer → scope (\_ → "_") do
                res ← act
                when (t /= Term BuiltinsVar) $ stackLog \p → p res
                pure res
              Check t' → scope (\p → p t') act
{-# INLINE logAndRunInfer #-}

withBlockLog ∷ (Has Checker sig m) ⇒ Term → m a → m a
withBlockLog into act = case into of
  Term Block{} → act
  _ → stackScope (\_ → "in") act

--

numFitsInto ∷ Integer → NumDesc → Bool
numFitsInto x d =
  numDecDispatch
    d
    (\(_ ∷ Proxy e) → fromIntegral (minBound @e) <= x && fromIntegral (maxBound @e) >= x)
    True

insideEra ∷ (Has Context sig m) ⇒ m a → m a
insideEra = local @IsErased (\_ → IsErased True)

insideQuant ∷ (Has Checker sig m) ⇒ Quant → m a → m a
insideQuant q = case q of
  QEra → insideEra
  QNorm → id

-- | Check, instantly unwrapping a layer
pattern CheckL ∷ () ⇒ (a2 ~ ()) ⇒ TermF Dyn → (Epoch, InferMode a2)
pattern CheckL x ← (e, Check (fDyn e → x))

-- TODO: Doesn't typecheck `id ex` (look test/id.fad).
-- The challenge: Term `t` has some type in context `Γ`, yet we need to check it against type `T` in context `Γ \/ whatever_inferapp_introduced`?
inferApp ∷ (Has Checker sig m) ⇒ Term → Vector (Quant, Term) → (Epoch, InferMode a) → m a
inferApp f0 args0 (em, mode) = case f0 of
  Term (App f' a') → inferApp f' ((QNorm, a') <| args0) (em, mode)
  Term (AppErased f' a') → inferApp f' ((QEra, a') <| args0) (em, mode)
  _ → do
    foldr
      ( \(q, arg) cont (args, f) →
          f
            & withMono'
              (q == QNorm, True)
              (mapTermFor mode)
              ( case q of
                  QNorm → Term <$> (Pi QNorm Nothing <$> subExVar (Term $ Builtin Any') <*> (Lambda <$> subExVar (Term $ Builtin Any')))
                  QEra → stackError \_ → "Cannot apply erased argument to unknown"
              )
              ( \t →
                  getEpoch >>= \e → case fDyn e t of
                    Pi q2 _n inT outT | q == q2 → do
                      arg' ← normalize arg
                      outT' ← fetchLambda outT >>= (`applyLambda` arg')
                      cont (args |> (q, arg, inT), outT')
                    _ → stackError \p → "inferApp" <+> pretty (show q) <+> p t
              )
      )
      ( \(args, outT0) → do
          outT ← dyn outT0
          let
            checkArgs = for_ args \(q, arg, argTy) → insideQuant q . infer arg . Check =<< fetchT argTy
          case mode of
            Infer → checkArgs *> fetchT outT
            Check (Dyn em → cOutT) → do
              uncurry subtype =<< (,) <$> fetchT outT <*> fetchT cOutT
              checkArgs
      )
      args0
      . ([],)
      =<< infer f0 Infer

checkDepLam ∷ ∀ sig m. (Has Checker sig m) ⇒ Quant → Maybe Ident → Lambda Term → Dyn → Lambda Dyn → m ()
checkDepLam q i bod inT outT = do
  inT' ← fetchT inT
  outT' ← fetchLambda outT
  scopedVar (const pure) (q, i, Nothing, inT')
    $ infer (unLambda bod)
    $ Check
    $ unLambda outT'

checkDepPair ∷ ∀ sig m. (Has Checker sig m) ⇒ ((Quant, Term), (Quant, Term)) → (Dyn, Lambda Dyn) → m ()
checkDepPair ((lQ, l), (rQ, r)) (lT, rT) = do
  insideQuant lQ . infer l . Check =<< fetchT lT
  l' ← normalize l
  insideQuant rQ . infer r . Check =<< (`applyLambda` l') =<< fetchLambda rT

data LookupRes a
  = LookupFound !a
  | LookupMissing !(Vector Dyn) -- Visited keys
  | LookupUnknown

-- {- | Accepts `tag`, `row` and `record`. Provides access to the field `tag` in `row`,
-- performs refines if necessary.
-- -}
rowGet ∷ ∀ sig m a. (Has Checker sig m) ⇒ ((Term → m Term) → a → m a) → Term → (Term → m a) → Term → Term → m (LookupRes a)
rowGet mapTerm tag cont = go -- tag is source term
 where
  notARow x = stackError \p → "Not a row:" <+> p x
  go ∷ Term → Term → m (LookupRes a)
  go row record =
    withMono
      ( \f → \case
          LookupFound a → LookupFound <$> mapTerm f a
          LookupMissing tags → LookupMissing <$> for tags (dyn <=< f <=< fetchT) -- TODO: needed?
          LookupUnknown → pure LookupUnknown
      )
      ( do
          u ← subExVar $ Term $ Builtin Any'
          head ← subExVar $ typOf u
          tail ← subExVar $ rowOf u
          pure $ Term $ Concat (Term $ FieldsLit (FRow ()) [(tag, head)]) (FRow $ Lambda tail) -- Introduces new variable ?! And in few other places.
      )
      ( \t →
          getEpoch >>= \e → case t of
            (fDyn e → FieldsLit (FRow ()) (Vector' l)) →
              foldr
                ( \(n, v) rec → do
                    eqTag ← isEqUnify tag =<< fetchT n
                    case eqTag of
                      EqYes → LookupFound <$> (fetchT v >>= cont)
                      EqUnknown → pure LookupUnknown
                      EqNot → rec
                )
                (pure $ LookupMissing $ fst <$> l)
                l
            (fDyn e → Concat l (FRow r)) → do
              inL ← (`go` record) =<< fetchT l
              case inL of
                LookupMissing visited1 → do
                  visited1' ← traverse fetchT visited1
                  let
                    select f = normalize $ Term $ App (Term $ App (Term $ Builtin f) $ Term $ ListLit $ Vector' visited1') record
                  recordL ← select RecordKeepFields
                  recordR ← select RecordDropFields
                  r' ← fetchLambda r >>= \r' → applyLambda r' recordL >>= \row' → go row' recordR
                  case r' of
                    LookupMissing visited2 → pure $ LookupMissing $ visited1 <> visited2
                    o → pure o
                o → pure o
            x → notARow x
      )
      row

-- | For each pair in the right RecordLit finds a pair and exeutes `f` on it. Accept "original right term" just for prettyprinting the error.
forRightFields ∷ (Has Checker sig m) ⇒ (tag1 → m Term) → (t1 → t2 → m ()) → Dyn → Vector (tag1, t1) → Vector (Dyn, t2) → m ()
forRightFields fetchTag1 f orig2 =
  foldM_
    ( \fields1' (tag2, ty2) →
        ifoldr
          ( \i (tag, ty) rec →
              ((,) <$> fetchTag1 tag <*> fetchT tag2) >>= uncurry isEqUnify >>= \case
                EqYes → do
                  f ty ty2
                  pure $ deleteAt i fields1'
                EqUnknown →
                  fetchTag1 tag >>= \tag' →
                    fetchT tag2 >>= \tag2' →
                      stackError \p → "Unable to check field equality when subtyping:" <+> p tag' <+> "?=" <+> p tag2'
                EqNot → rec
          )
          (fetchT tag2 >>= \tag' → fetchT orig2 >>= \orig2' → stackError \p → "Can't find" <+> p tag' <+> "in" <+> p orig2')
          fields1'
    )

refineGet ∷ (Has Checker sig m) ⇒ Int → (Int, Maybe Ident) → Term → m Term
refineGet var (skips0, etagSearched) = go 0
 where
  go skipped ty =
    if skipped >= skips0 && isNothing etagSearched
      then pure ty
      else
        withMono'
          (True, False)
          id
          (stackError \_ → "Cannot get erased refinement of unknown")
          ( unTerm >>> \case
              -- TODO: If we're being honest, `applyLambda` here is a horrible hack, since we apply a NON-NORMALIZED value to the lambda.
              Refine (RefinePreTy etagCurr ann base)
                | skipped >= skips0, Just es ← etagSearched, es == etagCurr → pure ann
                | otherwise → go (skipped + 1) =<< applyLambda base (Term $ RefineGet var (skipped, Just etagCurr))
              Refine (RefinePostTy base etagCurr ann)
                | skipped >= skips0, Just es ← etagSearched, es == etagCurr → pure $ applyLambdaRefineGetSkip var (skipped + 1) ann
                | otherwise → go (skipped + 1) base
              _ → stackError \_ → "TODO couldn't execute .@"
          )
          ty

checkList ∷ (Has Checker sig m) ⇒ Vector Term → Dyn → m ()
checkList els ty = for_ els \el → infer el . Check =<< fetchT ty

inferList ∷ (Has Checker sig m) ⇒ Vector Term → m (Maybe Term)
inferList tts = for (viewl tts) \(t, ts) → do
  tT ← dyn =<< infer t Infer
  checkList ts tT
  fetchT tT

-- TODO: Remove? Was previously used for Pi ?
-- match Row^ and Type^, since any Row^ is Type^
isTypePlus ∷ Term → Bool
isTypePlus =
  unTerm >>> \case
    Builtin TypePlus → True
    Builtin RowPlus → True
    _ → False

-- | Pi, Concat, Refine
checkT2 ∷ (Has Checker sig m) ⇒ Maybe Ident → Term → Lambda Term → (Term → Term) → Dyn → m ()
checkT2 i a b con u = do
  infer a . Check . con =<< fetchT u
  a' ← normalize a
  scopedVar (const pure) (QNorm, i, Nothing, a')
    . infer (unLambda b)
    . Check
    . con
    . nested
    =<< fetchT u

inferT2 ∷ (Has Checker sig m) ⇒ Maybe Ident → Term → Lambda Term → (Term → Term) → m Term
inferT2 i a b con =
  scopedExVar id (Term $ Builtin Any') $ dyn >=> \u1 →
    -- TODO: Good enough, or stricter?
    scopedExVar id (Term $ Builtin Any') $ dyn >=> \u2 → do
      infer a . Check . con =<< fetchT u1
      a' ← normalize a
      scopedVar (const pure) (QNorm, i, Nothing, a')
        . infer (unLambda b)
        . Check
        . con
        . nested
        =<< fetchT u2
      normalize . con =<< (maxOf <$> fetchT u1 <*> fetchT u2)

-- | Accepts a term and lifts it into the current scope.
nestBinding ∷ (Has Checker sig m) ⇒ Int → Term → m Term
nestBinding fromScope term0 = do
  currScope ← getScopeId
  let term = nestedByP term0 $ currScope - fromScope
  Scopes _ _ rs ← get
  stackLog \_ → "Trying nesting"
  case viewr rs of
    Just (_, (lastRewroteAtScope, _)) | lastRewroteAtScope >= fromScope → (stackLog \_ → "Nested") *> normalize term
    _ → pure term

-- | If input is a kind, returns universe level.
withMonoUniverse ∷ (Has Checker sig m) ⇒ ((Term → m Term) → a → m a) → (Term → m a) → Term → m a
withMonoUniverse mapTerm f =
  withMono mapTerm (typOf <$> subExVar (Term $ Builtin Any')) $ unTerm >>> \case
    App (isTypePlus → True) u → f u
    t → stackError \p → p (Term t) <+> "is not a kind"

-- | Either infers a normalized type for the value and context, or checks a value against the normalized type.
infer ∷ ∀ sig m a. (Has Checker sig m) ⇒ Term → InferMode a → m a
infer = logAndRunInfer $ \case
  -- Here, we will convert Checks to Infers.
  -- However, converting Infer to a Check when checking a term is hereby declared a deadly sin.
  (_, CheckL (Builtin Any')) → pure ()
  (Block (BlockLet q name tyM val into), mode0) → do
    ty ← stackScope (\_ → "let" <+> pQuant q <> maybe "_" pIdent name)
      $ insideQuant q
      $ case tyM of
        Nothing → infer val Infer
        Just ty → do
          ty' ← normalize ty
          infer val $ Check ty'
          pure ty'
    val' ← normalize val
    let
      fInto ∷ ((Term → m Term) → a → m a) → InferMode a → m a
      fInto mapTerm mode = scopedVar mapTerm (q, name, Just val', ty) $ infer (unLambda into) mode
    withBlockLog (unLambda into) $ case mode0 of
      (_, Infer) → fInto id Infer
      (e, Check subty0) → do
        subty ← fetchT $ Dyn e subty0
        fInto (const pure) $ Check $ nested subty
  (Block (BlockRewrite prf inner), mode) → do
    prfTy0 ← insideEra $ infer prf Infer
    let
      intoRewr = \case
        Term (Pi QEra _ (Term (Builtin Any')) into) → (\(Rewrite locs lfromto) → Rewrite (locs + 1) lfromto) <$> intoRewr (unLambda into)
        Term (App (Term (App (Term (Builtin Eq)) from)) to) → pure $ Rewrite 0 $ Lambda (from, to)
        t → stackError \p → p t <+> "is not a valid rewrite"
    stackLog \p → "(with rewrite" <+> p prfTy0 <> ")"
    rewr ← intoRewr prfTy0
    withBlockLog inner case mode of
      (_, Infer) → withRewr rewr $ infer inner Infer
      (e, Check ty) → withRewr rewr $ infer inner . Check =<< normalize =<< fetchT (Dyn e ty)
  (Import (fromMaybe (error "unresolved import") → n) _, (_, Infer)) → do
    Imports imps ← ask
    pure $ maybe (error "Incomplete context") snd $ imps !? n
  -- main
  (NumLit x, CheckL (Builtin (Int' d))) →
    if x `numFitsInto` d
      then pure ()
      else stackError \_ → "Number literal " <> pretty x <> " does not fit into " <> pIdent (identOfBuiltin $ Int' d)
  (NumLit x, (_, Infer)) →
    pure
      $ Term
      $ Builtin
      $ Int'
      $ let candidates = NumFin False <$> [Bits8, Bits16, Bits32, Bits64]
         in fromMaybe NumInf $ find @[] (x `numFitsInto`) candidates
  (TagLit _, (_, Infer)) → pure $ Term $ Builtin Tag
  (BoolLit _, (_, Infer)) → pure $ Term $ Builtin Bool
  (ListLit (Vector' values), (e, Check (Term (App (Term (Builtin List)) (Dyn e → ty))))) → checkList values ty
  (ListLit (Vector' values), (_, Infer)) → Term . App (Term $ Builtin List) . fromMaybe (Term $ Builtin Never) <$> inferList values
  (FieldsLit (FRecord ()) flds, (_, Infer)) → do
    rowFields ← for flds \(n, v) → do
      infer n $ Check $ Term $ Builtin Tag
      vTy ← infer v Infer
      pure (n, vTy)
    pure $ Term $ FieldsLit (FRow ()) rowFields
  (FieldsLit (FRecord ()) (Vector' flds), (e, Check b@(fDyn e → FieldsLit (FRow ()) (Vector' flds2)))) →
    forRightFields pure (\f t → infer f . Check =<< fetchT t) (Dyn e b) flds flds2
  (FieldsLit (FRow ()) (Vector' flds), (_, Infer)) → do
    -- TODO: use maxOf chain
    for_ flds \(n, _) → infer n $ Check $ Term $ Builtin Tag
    inferList (snd <$> flds) >>= withMonoUniverse id (pure . rowOf) . fromMaybe typ
  (FieldsLit (FRow ()) (Vector' flds), (e, Check (unTerm → App (isTypePlus → True) (Dyn e . typOf → ty)))) → do
    for_ flds \(n, _) → infer n $ Check $ Term $ Builtin Tag
    checkList (snd <$> flds) ty
  (BuiltinsVar, (_, Infer)) →
    pure
      $ Term
      $ FieldsLit (FRow ())
      $ Vector'
      $ (\b → (Term $ TagLit $ identOfBuiltin b, typOfBuiltin b))
      <$> builtinsList
  (Builtin x, (_, Infer)) → pure $ typOfBuiltin x
  (Lam q1 n1 bod, CheckL (Pi q2 n2 inT outT)) | q1 == q2 → checkDepLam q1 (n1 <|> n2) bod inT outT
  (term, CheckL (Pi QEra _ xTy yT)) → do
    xTy' ← fetchT xTy
    scopedUniVar (const pure) xTy' \uni →
      infer (Term term) . Check =<< (`applyLambda` uni) =<< fetchLambda yT
  (Lam QNorm n bod, (_, Infer)) →
    scopedExVar id (Term $ Builtin Any') $ dyn >=> \inT → do
      outT ← fetchT inT >>= \inT' → scopedVar id (QNorm, n, Nothing, inT') $ infer (unLambda bod) Infer
      fetchT inT <&> \inT' → Term $ Pi QNorm Nothing inT' $ Lambda $ nested outT
  (Lam QEra _ _, (_, Infer)) → stackError \_ → "TODO Cannot infer a type of an erased lambda" -- Probably we could, but the idea overall is oxymoron.
  (App (unTerm → App (unTerm → Builtin RecordGet) tag) record, mode) → do
    infer tag $ Check $ Term $ Builtin Tag
    let
      mapTerm ∷ (Term → m Term) → a → m a
      cont ∷ Term → m a
      (mapTerm, cont) = case mode of
        (_, Infer) → (id, pure)
        (e, Check ty2) → (const pure, \ty → subtype ty =<< fetchT (Dyn e ty2))
    row0 ← infer record Infer
    tag' ← normalize tag
    record' ← normalize record
    res ←
      rowGet
        mapTerm
        tag'
        cont
        row0
        record'
    case res of
      LookupFound x → pure x
      LookupMissing d →
        for d fetchT >>= \d' → stackError \p →
          "Couldn't find field" <+> p tag' <+> "among" <+> list (p <$> toList d')
      LookupUnknown → stackError \_ → "Can't check if tag is equal"
  (App f a, mode) → inferApp f [(QNorm, a)] mode
  (Var i, (_, Infer)) → do
    Scopes binds _ _ ← get @Scopes
    IsErased isEra ← ask
    let scope = length binds - i - 1
    case binds !? scope of
      Just (q, _, _, ty) | isEra || q == QNorm → do
        stackLog \p → "var" <+> pretty i <+> ":" <+> p ty
        nestBinding scope ty
      _ → stackError \_ → "Unknown var #" <> pretty i
  (Sorry, (_, Check k)) → stackLog \p → annotate (color Yellow) $ "sorry :" <+> p k
  (Sorry, (_, Infer)) → stackError \_ → "sorry"
  (RefineGet i (skips, final), (_, Infer)) → do
    IsErased isEra ← ask
    when (isJust final && not isEra) $ stackError \_ → "Can't access erased refinement in normal context"
    iT ← infer (Term $ Var i) Infer
    refineGet i (skips, final) iT
  (AppErased f a, mode) → inferApp f [(QEra, a)] mode
  (Refine (RefinePre ann base), CheckL (Refine (RefinePreTy _n annT baseT))) → checkDepPair ((QEra, ann), (QNorm, base)) (annT, baseT)
  (Refine (RefinePost base ann), CheckL (Refine (RefinePostTy baseT _n annT))) → checkDepPair ((QNorm, base), (QEra, ann)) (baseT, annT)
  (Refine (RefinePre{}), (_, Infer)) → stackError \_ → "TODO Cannot infer a type of an erased annotation"
  (Refine (RefinePost{}), (_, Infer)) → stackError \_ → "TODO Cannot infer a type of an erased annotation"
  (Concat l (FRecord r), CheckL (Concat aT (FRow bT))) → checkDepPair ((QNorm, l), (QNorm, r)) (aT, bT)
  (Concat l (FRecord r), (_, Infer)) →
    Term
      <$> ( Concat
              <$> infer l Infer
              <*> (FRow . Lambda . nested <$> infer r Infer)
          )
  -- type
  (Refine (RefinePreTy i annT baseT), CheckL (App (Dyn _ (unTerm → Builtin TypePlus)) u)) → checkT2 (Just i) annT baseT typOf u
  (Refine (RefinePreTy i annT baseT), (_, Infer)) → inferT2 (Just i) annT baseT typOf
  (Refine (RefinePostTy baseT _ annT), CheckL (App (Dyn _ (unTerm → Builtin TypePlus)) u)) → checkT2 (Just dotvar) baseT annT typOf u
  (Refine (RefinePostTy baseT _ annT), (_, Infer)) → inferT2 (Just dotvar) baseT annT typOf
  (Pi _q i inTy outTy, CheckL (App (Dyn _ (unTerm → Builtin TypePlus)) u)) → checkT2 i inTy outTy typOf u
  (Pi _q i inTy outTy, (_, Infer)) → inferT2 i inTy outTy typOf
  (Concat l (FRow r), CheckL (App (Dyn _ (isTypePlus → True)) u)) → checkT2 (Just dotvar) l r rowOf u
  (Concat l (FRow r), (_, Infer)) → inferT2 (Just dotvar) l r rowOf
  (UniVar _ ty, (_, Infer)) → pure ty
  (ExVar (scopeid, subid), (_, Infer)) → do
    Scopes _ exs _ ← get @Scopes
    let
      (exScope, ty) = fromMaybe (error "Ex not found in scope") do
        (_, scope) ← exs !? scopeid
        i ←
          findIndexL
            ( \case
                EVar subid2 _ → subid == subid2
                _ → False
            )
            scope
        EVar _ (Right ty') ← scope !? i
        pure (scopeid, ty')
    nestBinding exScope ty
  (t, (e, Check c@(fDyn e → Refine (RefinePostTy baseT _n annT)))) → do
    annT' ← uncurry applyLambda =<< (,) <$> fetchLambda annT <*> normalize (Term t)
    case annT' of
      TBuiltin Eq `TApp` a `TApp` b →
        isEqUnify a b >>= \case
          -- TODO: Drop unify?
          EqYes → infer (Term t) . Check =<< fetchT baseT
          _ → viaInfer t e c
      _ → viaInfer t e c
  (t, (e, Check c)) → viaInfer t e c
 where
  viaInfer t e c = stackScope (\p → "check via infer" <+> p (Term t) <+> ":" <+> p c) do
    ty ← infer (Term t) Infer
    (ty `subtype`) =<< fetchT (Dyn e c)

typOfBuiltin ∷ BuiltinT → Term
typOfBuiltin = \case
  Any' → [termQQ| Type^ 0 |]
  Bool → [termQQ| Type^ 0 |]
  Eq → [termQQ| Fun (Any) (Any) -> Type^ 0 |]
  Loop → [termQQ| Fun {I} {measure : Fun (I) -> Int+} {O} (I) (Fun (curr : I) (Fun (next : I) {_ : Where (measure next < measure curr)} -> O) -> O) -> O|]
  If → [termQQ| Fun {A} (cond : Bool) (Fun {_ : Eq cond true} -> A) (Fun {_ : Eq cond false} -> A) -> A |]
  Int' _d → [termQQ| Type^ 0 |]
  IntAdd d → op2d d
  IntEq → [termQQ| Fun (Int) (Int) -> Bool |]
  IntGte0 → [termQQ| Fun (Int) -> Bool |]
  IntMul d → op2d d
  IntNeg d → opd d
  List → [termQQ| Fun {u} (Type^ u) -> Type^ u |]
  ListIndexL → [termQQ| Fun {A} (i : Int+) (l : List A) {_ : Where (i < list_length l)} -> A |]
  ListLength → [termQQ| Fun {A} (List A) -> Int+ |]
  ListViewL → [termQQ| Fun {A} (l : List A) {_ : Where (0 < list_length l)} -> {( .left = A | .rest = List A )}|]
  Never → [termQQ| Type^ 0 |]
  PropListViewlDec → [termQQ| Fun {A} (l : List A) -> Eq (list_length l) (list_length (list_viewl l).rest + 1) |]
  PropLteTrans → [termQQ| Fun {a} {b} {c} (Where (a <= b)) (Where (b <= c)) -> Where (a <= c) |]
  RecordDropFields → [termQQ| Fun {u : Int} {row : Row^ u} (List Tag) (row) -> Any |]
  RecordGet → [termQQ| Fun {u : Int} {row : Row^ u} {T : Type^ u} (tag : Tag) (record : {( (tag) = T )} \/ row) -> T|]
  RecordKeepFields → [termQQ| Fun {u : Int} {row : Row^ u} (List Tag) (row) -> Any |]
  -- TODO: Better type
  Refl → [termQQ| Fun {x} -> Eq x x |]
  RowPlus → [termQQ| Fun (u : Int+) -> Type^ u |]
  Tag → [termQQ| Type^ 0 |]
  TagEq → [termQQ| Fun (Tag) (Tag) -> Bool |]
  TypePlus → [termQQ| Fun (u : Int+) -> Type^ (u + 1) |]
  W → [termQQ| Fun {u} (Type^ u) -> Type^ u |]
  WUnwrap → [termQQ| Fun {A} (W A) -> A |]
  WWrap → [termQQ| Fun {A} (A) -> W A |]
 where
  opd d = Term $ Pi QNorm Nothing (Term $ Builtin $ Int' d) $ Lambda $ Term $ Builtin $ Int' d
  op2d d = Term $ Pi QNorm Nothing (Term $ Builtin $ Int' d) $ Lambda $ opd d

-- TODO: Allow instantiation with erased functions

-- | Instantiate meta to a normalized value
instMeta ∷ ∀ sig m. (Has Checker sig m) ⇒ (Int, Int) → Term → m ()
instMeta = (\f a b → stackScope (\_ → "instMeta") $ f a b) \(scope1, sub1) →
  let
    getOrd (scopeI, subI) = do
      Scopes _ exs _ ← get @Scopes
      let exsLen = length exs
      pure $ (scopeI,) $ fromMaybe (error $ "Ex not found in scope: scopeI=" <> show scopeI <> ", subI=" <> show subI <> ", exsLen=" <> show exsLen) do
        (_, scope) ← exs !? scopeI
        findIndexL
          ( \case
              EMarker → False
              ERewrite{} → False
              EVar subI2 _ → subI == subI2
              EUniVar subI2 → subI == subI2
          )
          scope
    instMeta' ∷ Int → Term → m Term
    instMeta' locs t0 =
      getEpoch >>= \e → case fDyn e t0 of
        ExVar (scope2, sub2) → do
          (ord1, ord2) ← (,) <$> getOrd (scope1, sub1) <*> getOrd (scope2, sub2)
          if ord2 <= ord1
            then pure $ Term $ ExVar (scope2, sub2)
            else do
              u ← fresh
              Scopes _ exs _ ← get @Scopes
              let
                t2 = fromMaybe (error $ "Ex not found in scope (instMeta'): ord2=" <> show ord2 <> ", exsLen=" <> show (length exs)) do
                  (_, scope) ← exs !? fst ord2
                  EVar _ (Right ty) ← scope !? snd ord2
                  pure ty
              t2' ← instMeta' locs t2 -- TODO RECHECK: gracefully moves t2 to a new location?
              writeExBefore [(u, t2')] (scope1, sub1)
              writeMeta (scope2, sub2) (locs, Term $ ExVar (scope1, u))
              pure $ Term $ ExVar (scope1, u)
        UniVar uni2 _ → do
          (ord1, ord2) ← (,) <$> getOrd (scope1, sub1) <*> getOrd uni2
          if ord2 <= ord1
            then pure t0
            else stackError \_ → "Attempting to assign existential to later introduced universal"
        App (Dyn _ (Term (Builtin W))) (Dyn _ a) → pure $ Term $ Term (Builtin W) `App` a
        -- Literals
        NumLit x → pure $ Term $ NumLit x
        TagLit x → pure $ Term $ TagLit x
        BoolLit x → pure $ Term $ BoolLit x
        FieldsLit fi flds → Term . FieldsLit fi <$> traverse (bitraverse (instMeta' locs <=< fetchT) (instMeta' locs <=< fetchT)) flds
        Builtin x → pure $ Term $ Builtin x
        Lam QNorm i a → Term . Lam QNorm i . Lambda <$> (instMeta' (locs + 1) . unLambda =<< fetchLambda a)
        App f a → do
          f' ← instMeta' locs =<< fetchT f
          a' ← instMeta' locs =<< fetchT a
          pure $ Term $ App f' a'
        Var x → pure $ Term $ Var x
        Sorry → pure $ Term Sorry -- questionable
        RefineGet i (skips, Just f) → pure $ Term $ RefineGet i (skips, Just f)
        Refine (RefinePreTy n annTy base) →
          Term
            . Refine
            <$> (RefinePreTy n <$> (instMeta' locs =<< fetchT annTy) <*> fmap Lambda (instMeta' (locs + 1) . unLambda =<< fetchLambda base))
        Refine (RefinePostTy base n annTy) →
          Term
            . Refine
            <$> (RefinePostTy <$> (instMeta' locs =<< fetchT base) <*> pure n <*> fmap Lambda (instMeta' (locs + 1) . unLambda =<< fetchLambda annTy))
        Pi QNorm n inT outT → do
          inT' ← instMeta' locs =<< fetchT inT
          outT' ← instMeta' (locs + 1) . unLambda =<< fetchLambda outT
          pure $ Term $ Pi QNorm n inT' $ Lambda outT'
        Concat a (FRecord b) →
          Term
            <$> ( Concat
                    <$> (instMeta' locs =<< fetchT a)
                    <*> (FRecord <$> (instMeta' locs =<< fetchT b))
                )
        Concat a (FRow b) →
          Term
            <$> ( Concat
                    <$> (instMeta' locs =<< fetchT a)
                    <*> (FRow . Lambda <$> (instMeta' (locs + 1) . unLambda =<< fetchLambda b))
                )
        _ → stackError \p → "instMeta (of" <+> pretty (scope1, sub1) <> ")" <+> p t0
   in
    \val →
      let r = writeMeta (scope1, sub1) . (0,) =<< instMeta' 0 val
       in case val of
            Term (ExVar var2) →
              unless ((scope1, sub1) == var2) r
            _ → r

isEqUnify ∷ (Has Checker sig m) ⇒ Term → Term → m EqRes
isEqUnify = isEq' (\a b → instMeta a b $> True)

-- -- TODO: Use isEq.

pattern IfT ∷ Term → Term → Term → Term
pattern IfT cond a b ← Term (App (Term (App (Term (App (Term (Builtin If)) cond)) a)) b)

-- -- | a <: b Check if type `a` is a subtype of type `b`.
subtype ∷ ∀ sig m. (Has Checker sig m) ⇒ Term → Term → m ()
subtype = \a b →
  stackScope (\p → p a <+> annotate (color Cyan) "<:" <+> p b) $ subtype' a b
 where
  -- Core subtyping logic based on the structure of the resolved types.
  subtype' ∷ Term → Term → m ()
  subtype' t10 t20 =
    getEpoch >>= \e → case (t10, t20) of -- TODO: fDyn e right here? Maybe in infer?
      -- Subtype Pi & RefinePreTy directly if possible. Can misfire, but generally ensures `A <: B` gets correctly subtyped when `A = B`.
      (fDyn e → Pi q1 n1 inT1 outT1, fDyn e → Pi q2 n2 inT2 outT2) | q1 == q2 && (q1 == QNorm || n1 == n2) → do
        uncurry subtype =<< (,) <$> fetchT inT2 <*> fetchT inT1 -- Input types are contravariant (T2 <: T1)
        fetchT inT2 >>= \inT2' → do -- Output types are covariant
          outT1' ← fetchLambda outT1
          outT2' ← fetchLambda outT2
          scopedVar (const pure) (QNorm, n1 <|> n2, Nothing, inT2') $ subtype (unLambda outT1') (unLambda outT2')
      (fDyn e → Refine (RefinePreTy n1 annT1 baseT1), fDyn e → Refine (RefinePreTy n2 annT2 baseT2)) | n1 == n2 → do
        uncurry subtype =<< (,) <$> fetchT annT1 <*> fetchT annT2
        fetchT annT2 >>= \inT2' → do
          outT1' ← fetchLambda baseT1
          outT2' ← fetchLambda baseT2
          scopedVar (const pure) (QNorm, Just n2, Nothing, inT2') $ subtype (unLambda outT1') (unLambda outT2')
      -- Handle existentials now
      (unTerm → Refine (RefinePreTy _n annT baseT), t) →
        scopedUniVar (const pure) annT ((`subtype` t) <=< applyLambda baseT)
      (t, unTerm → Pi QEra (Just _n) inT outT) →
        scopedUniVar (const pure) inT (subtype t <=< applyLambda outT)
      (t, unTerm → Refine (RefinePreTy n annT baseT)) →
        scopedExVar (\_ _ → stackError \_ → "Unresolved existential" <+> pIdent n) annT (subtype t <=< applyLambda baseT)
      (unTerm → Pi QEra (Just n) inT outT, t) →
        scopedExVar (\_ _ → stackError \_ → "Unresolved existential" <+> pIdent n) inT ((`subtype` t) <=< applyLambda outT)
      -- Existential Variables (?a <: ?b, ?a <: T, T <: ?a)
      (fDyn e → ExVar ex1, fDyn e → ExVar ex2) | ex1 == ex2 → pure ()
      (fDyn e → ExVar ex1, t2) → instMeta ex1 t2
      (t1, fDyn e → ExVar ex) → instMeta ex t1
      -- Universal Variables (u1 <: u2) - Must be identical.
      (fDyn e → UniVar id1 _, fDyn e → UniVar id2 _) | id1 == id2 → pure ()
      -- Refine post
      (fDyn e → Refine (RefinePostTy base1 _ ann1), fDyn e → Refine (RefinePostTy base2 n ann2)) → do
        uncurry subtype =<< (,) <$> fetchT base1 <*> fetchT base2
        fetchT base1 >>= \base1' → do
          ann1' ← fetchLambda ann1
          ann2' ← fetchLambda ann2
          scopedVar (const pure) (QNorm, Just n, Nothing, base1') $ subtype (unLambda ann1') (unLambda ann2')
      (unTerm → Refine (RefinePostTy base _ _ann), t) → subtype base t
      -- Function Types (Πx:T1.U1 <: Πy:T2.U2)
      (fDyn e → Builtin (Int' d1), fDyn e → Builtin (Int' d2)) →
        let fits = case (d1, d2) of
              (_, NumInf) → True
              (NumFin nonneg1 bits1, NumFin nonneg2 bits2) → case (nonneg1, nonneg2) of
                (True, False) → bits1 < bits2
                (False, True) → False
                _ → bits1 <= bits2
              (NumInf, NumFin{}) → False
         in if fits then pure () else stackError \_ → "Cannot fit " <> pIdent (identOfBuiltin $ Int' d1) <> " into " <> pIdent (identOfBuiltin $ Int' d2)
      (fDyn e → Builtin Never, _) → pure ()
      (_, fDyn e → Builtin Any') → pure ()
      -- Builtin Types (must be identical)
      (fDyn e → Builtin a, fDyn e → Builtin b) | a == b → pure ()
      (fDyn e → Var i, fDyn e → Var j) | i == j → pure ()
      -- Type Universes (Type L1 <: Type L2 where L1 <= L2)
      (Term (App (fDyn e → Builtin TypePlus) a0), Term (App (fDyn e → Builtin TypePlus) b0)) → do
        case (a0, b0) of
          (fDyn e → NumLit 0, _) → pure () -- TODO: Remove?
          -- If one level is existential, unify it with the other level constraint.
          (fDyn e → ExVar ex, b) → instMeta ex b
          (a, fDyn e → ExVar ex) → instMeta ex a
          (a, b) →
            isEqUnify a b >>= \case
              -- Skippind `dyn`'s here since non-EqYes doesn't update a & b.
              EqYes → pure ()
              _ → do
                let negA = Term $ Term (Builtin $ IntNeg NumInf) `App` a
                evaluated ← normalize (TBuiltin IntGte0 `TApp` (TBuiltin (IntAdd NumInf) `TApp` b `TApp` negA))
                stackLog \p → p evaluated
                isEqUnify evaluated (Term $ BoolLit True) >>= \case
                  EqYes → pure ()
                  _ → stackError \p → "Cannot subtype universes with levels:" <+> p a <+> "≤" <+> p b <> line <> "Stuck at:" <+> p evaluated
      (Term (App (fDyn e → Builtin List) a), Term (App (fDyn e → Builtin List) b)) → subtype a b
      (Term (App (fDyn e → Builtin W) a), Term (App (fDyn e → Builtin W) b)) →
        isEqUnify a b >>= \case
          EqYes → pure ()
          _ → stackError \p → "Cannot equate wrapped types" <+> p a <+> "and" <+> p b
      (Term (App (fDyn e → Builtin RowPlus) a), Term (App (fDyn e → Builtin RowPlus) b)) → subtype (typOf a) (typOf b)
      (Term (App (fDyn e → Builtin RowPlus) a), Term (App (fDyn e → Builtin TypePlus) u)) → subtype (typOf a) (typOf u)
      (fDyn e → FieldsLit (FRow ()) (Vector' fields1), b@(fDyn e → FieldsLit (FRow ()) (Vector' fields2))) → do
        forRightFields fetchT (\ty ty2 → uncurry subtype =<< ((,) <$> fetchT ty <*> fetchT ty2)) (Dyn e b) fields1 fields2
      -- l1 \./ r1  <: l2 \./ r2
      (fDyn e → Concat l1 (FRow lr1), fDyn e → Concat l2 (FRow lr2)) → do
        uncurry subtype =<< ((,) <$> fetchT l1 <*> fetchT l2)
        fetchT l1 >>= \l1' → do
          body1' ← fetchLambda lr1
          body2' ← fetchLambda lr2
          scopedVar (const pure) (QNorm, Just dotvar, Nothing, l1') do
            subtype (unLambda body1') (unLambda body2')
      (a, IfT (Dyn e → cond) (Dyn e → th) (Dyn e → el)) → do
        let
          branch assumes br = do
            cond' ← fetchT cond
            withRewr (Rewrite 0 $ Lambda (cond', Term $ BoolLit assumes)) do
              a' ← normalize a
              subtype a' =<< fetchT br
        branch True th
        branch False el
      -- Catch-all: if no rule matches, check equality
      (t1, t2) →
        isEqUnify t1 t2 >>= \case
          EqYes → pure ()
          _ → stackError \p → "Subtype check failed, no rule applies for:" <+> p t1 <+> "<:" <+> p t2

runChecker' ∷ (Applicative m) ⇒ UsedNames → StateC UsedNames (FreshC (ErrorC e m)) a → m (Either e a)
runChecker' n =
  runError (pure . Left) (pure . Right)
    . evalFresh 0
    . evalState n

checkModule' ∷ (Has (State UsedNames :+: Throw (Doc AnsiStyle) :+: Fresh :+: StackLog) sig m) ⇒ Module → m Term
checkModule' = \(Module m) → snd . maybe (error "module must be non-empty") snd . viewr <$> foldlM checkSubModule [] m
 where
  checkSubModule xs x = (xs |>) <$> runSubContext (Imports xs) ((,) <$> normalize x <*> infer x Infer)

checkModule ∷ (UsedNames, Module) → IO ()
checkModule (names, m) = do
  (stacks, res) ← runStackAccC $ runChecker' names $ checkModule' m
  render case res of
    Left e →
      pStacks stacks
        <> line
        <> annotate (color Red) "error: "
        <> e
    Right r → pTerm [] r

-- Loads, checks, builds
build' ∷ OsPath → IO (Vector OsPath)
build' path' = do
  (names, m, paths) ← loadModule' path'
  checkModule (names, m)
  writeFile' (path' `replaceExtension` unsafeEncodeUtf ".fadobj")
    $ serializeCompileResult
    $ compileModule m
  pure paths

build ∷ FilePath → IO ()
build = void . (encodeUtf >=> build')

watch ∷ FilePath → IO ()
watch path = do
  path' ← encodeUtf path
  let
    getModTimes files = do
      tms ← for files \p → getModificationTime (p <> unsafeEncodeUtf ".fad")
      pure $ zip files tms
    rebuild = do
      render $ annotate (color Yellow) "Rebuilding..."
      res ← tryAny (build' path')
      case res of
        Left e → print e *> getModTimes [path'] -- horrible
        Right paths → getModTimes paths -- TODO: fragile & doesn't work. Just stop throwing errors.
    loop ∷ Vector (OsPath, UTCTime) → IO never
    loop oldTimes = do
      threadDelay 50000 -- 0.05s
      newTimes ← getModTimes $ fst <$> oldTimes
      if oldTimes /= newTimes
        then rebuild >>= loop
        else loop oldTimes
  render $ annotate (color Yellow) $ "Watching " <> pretty path
  rebuild >>= loop

checkModuleDebug ∷ (UsedNames, Module) → IO ()
checkModuleDebug (names, m) = do
  res ← runStackPrintC $ runChecker' names $ checkModule' m
  render case res of
    Left e → annotate (color Red) "error: " <> e
    Right r → pTerm [] r

main ∷ IO ()
main = getArgs >>= \case
  [] -> render $ annotate (color Red) "Usage: fadeno <file>"
  (arg:_) -> watch arg
