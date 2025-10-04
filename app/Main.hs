{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use const" #-}
module Main where

import Control.Algebra
import Control.Carrier.Error.Church (ErrorC, runError)
import Control.Carrier.Fresh.Church (FreshC, evalFresh)
import Control.Carrier.Reader (ReaderC, runReader)
import Control.Carrier.State.Church (StateC)
import Control.Carrier.Writer.Church (WriterC, runWriter)
import Control.Effect.Error (throwError)
import Control.Effect.Fresh (Fresh, fresh)
import Control.Effect.Lift (Lift, sendIO)
import Control.Effect.Reader (Reader, ask, local)
import Control.Effect.State (get, modify, put, state)
import Control.Effect.Throw (Throw)
import Control.Effect.Writer (Writer, censor, tell)
import Data.Bitraversable (bimapM)
import Data.ByteString.Char8 (pack)
import Data.List (find)
import Data.RRBVector (Vector, adjust, adjust', deleteAt, findIndexL, ifoldr, replicate, splitAt, take, unzip, viewl, viewr, zip, (!?), (|>))
import Data.Type.Equality (type (~))
import GHC.Exts (IsList (..))
import Normalize (Context, Dyn (..), EEntry (..), Epoch (..), EqRes (..), Rewrite (..), Scopes (..), applyLambda, dyn, fDyn, fetchLambda, fetchT, getEpoch, getScopeId, isEq', normalize, normalize', numDecDispatch, runContext', runIsolate, splitAt3, termQQ, withBinding, withMarked)
import Parser (Bits (..), BlockF (..), BuiltinT (..), Fields (..), Ident (..), Lambda (..), NumDesc (..), Quant (..), Term (..), TermF (..), Vector' (..), builtinsList, identOfBuiltin, nested, nestedBy', nestedByP, pIdent, pQuant, pTerm, parse, render, rowOf, traverseTermF, typ, typOf, pattern IntND, pattern Op2)
import Prettyprinter (Doc, annotate, group, indent, line, list, nest, pretty, (<+>))
import Prettyprinter.Render.Terminal (AnsiStyle, Color (..), color)
import RIO hiding (Reader, Vector, ask, concat, drop, filter, link, local, replicate, runReader, take, to, toList, zip)

-- TODO: Permit inference of dependent Pis?
-- TODO: Concat uncomfortably replicates Pi.
-- TODO: There are few deadly sins (Infer → Check conversions) that should be removed. Infer should never invoke check! (Pi/inferList/???)

type Checker = Context :+: Fresh :+: StackLog :+: Throw (Doc AnsiStyle)

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
termLoggerM = (\(Scopes ctx _ _) → pTerm $ (\(q, n, _, _) → (q, n)) <$> ctx) <$> get @Scopes

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
scopedVar mapTerm (bindQ, bindI, bindT, bindTy) act =
  withBinding (bindQ, bindI, bindT, bindTy) act
    >>= mapTerm (\t → maybe (stackError \p → "Var leaked in" <+> p t) pure $ nestedBy' 0 t $ -1)

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

freshIdent ∷ (Has Fresh sig m) ⇒ m Ident
freshIdent = (`Ident` False) . ("/" <>) . pack . show <$> fresh

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
  -- | Unwrap Foralls
  Bool →
  ((Term → m Term) → a → m a) →
  -- | onMeta
  ReaderC Int (WriterC (Vector (Int, Term)) m) Term →
  -- | onOther
  (Term → m a) →
  Term →
  m a
withMono' foralls mapTerm onMeta onOther = go
 where
  go =
    unTerm >>> \case
      ExVar (scope, sub) → do
        (newExs, res) ← runWriter (curry pure) $ runReader scope onMeta
        writeExBefore newExs (scope, sub)
        writeMeta (scope, sub) (0, res)
        onOther res
      Pi QEra _n x y
        | foralls →
            stackScope (\_ → "(unwrapped forall)")
              $ scopedExVar
                mapTerm
                x
                (go <=< applyLambda y)
      r → onOther $ Term r

withMono ∷
  (Has Checker sig m) ⇒
  ((Term → m Term) → a → m a) →
  ReaderC Int (WriterC (Vector (Int, Term)) m) Term →
  (Term → m a) →
  Term →
  m a
withMono = withMono' True

data InferMode a where
  Infer ∷ InferMode Term
  Check ∷ Term → InferMode ()

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
    (\_ → True)

withEra ∷ (Has Context sig m) ⇒ m a → m a
withEra act = do
  quants ← state @Scopes \(Scopes binds es rs) →
    first (\x → Scopes x es rs)
      $ unzip ((\(q, a, b, c) → ((QNorm, a, b, c), q)) <$> binds)
  res ← act
  modify @Scopes \(Scopes bs es rs) →
    Scopes
      ((\(q, (_, a, b, c)) → (q, a, b, c)) <$> zip quants bs)
      es
      rs
  pure res

-- mapTermFor ∷ (Applicative f) ⇒ InferMode a → ((Term → f Term) → a → f a)
-- mapTermFor = \case
--   Infer → id
--   Check _ → const pure

-- | Check, instantly unwrapping a layer
pattern CheckL ∷ () ⇒ (a2 ~ ()) ⇒ TermF Dyn → (Epoch, InferMode a2)
pattern CheckL x ← (e, Check (fDyn e → x))

pattern InferL ∷ () ⇒ (a2 ~ Term) ⇒ (a1, InferMode a2)
pattern InferL ← (_, Infer)

inferApp ∷ (Has Checker sig m) ⇒ Quant → Term → Term → m Term
inferApp q f a = do
  let norm = q == QNorm
  infer f Infer
    >>= withMono'
      norm
      id
      ( if norm
          then Term <$> (Pi QNorm Nothing <$> subExVar (Term $ Builtin Any') <*> (Lambda <$> subExVar (Term $ Builtin Any')))
          else stackError \_ → "Cannot apply erased argument to unknown"
      )
      ( \t0 →
          getEpoch >>= \e0 → case t0 of
            (fDyn e0 → Pi q2 _n inT outT) | q == q2 → do
              let updCtx = if norm then id else withEra
              updCtx (infer a . Check =<< fetchT inT)
              uncurry applyLambda =<< ((,) <$> fetchLambda outT <*> normalize a)
            t → stackError \p → "inferApp" <+> pretty (show q) <+> p t
      )

checkDepLam ∷ ∀ sig m. (Has Checker sig m) ⇒ Quant → Maybe Ident → Lambda Term → Dyn → Lambda Dyn → m ()
checkDepLam q i bod inT outT = do
  inT' ← fetchT inT
  outT' ← fetchLambda outT
  scopedVar (const pure) (q, i, Nothing, inT')
    $ infer (unLambda bod)
    $ Check
    $ unLambda outT'

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
          LookupMissing a → pure $ LookupMissing a -- erased anyway, no point of mapping
          LookupUnknown → pure LookupUnknown
      )
      ( do
          u ← subExVar $ Term $ Builtin Any'
          head ← subExVar $ typOf u
          tail ← subExVar $ rowOf u
          pure $ Term $ Concat (Term $ FieldsLit (FRow ()) [(tag, head)]) (FRow (Nothing, Lambda tail))
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
            (fDyn e → Concat l (FRow (_, r))) → do
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

checkList ∷ (Has Checker sig m) ⇒ Vector Term → Dyn → m ()
checkList els ty = for_ els \el → infer el . Check =<< fetchT ty

inferList ∷ (Has Checker sig m) ⇒ Vector Term → m (Maybe Term)
inferList tts = for (viewl tts) \(t, ts) → do
  tT ← dyn =<< infer t Infer
  checkList ts tT
  fetchT tT

-- match Row^ and Type^, since any Row^ is Type^
isTypePlus ∷ Term → Bool
isTypePlus =
  unTerm >>> \case
    Builtin TypePlus → True
    Builtin RowPlus → True
    _ → False

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
      $ (if q == QEra then withEra else id)
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
    prfTy0 ← infer prf Infer
    let
      intoRewr = \case
        Term (Pi QEra _ (Term (Builtin Any')) into) → (\(Rewrite locs lfromto) → (Rewrite (locs + 1) lfromto)) <$> intoRewr (unLambda into)
        Term (App (Term (App (Term (Builtin Eq)) from)) to) → pure $ Rewrite 0 $ Lambda (from, to)
        t → stackError \p → p t <+> "is not a valid rewrite"
    stackLog \p → "(with rewrite" <+> p prfTy0 <> ")"
    rewr ← intoRewr prfTy0
    let
      fInto cont = do
        i ← getScopeId
        modify \(Scopes bs es rs) → Scopes bs (adjust' i (fmap (|> ERewrite rewr)) es) (rs |> (i, rewr))
        cont <* modify \(Scopes bs es rs) →
          Scopes
            bs
            (adjust' i (fmap $ maybe (error "Scope disappeared") fst . viewr) es)
            (maybe (error "Rewrite disappeared") fst $ viewr rs)
    withBlockLog inner case mode of
      (_, Infer) → fInto $ infer inner Infer
      (e, Check ty) → fInto $ infer inner . Check =<< normalize =<< fetchT (Dyn e ty)
  (Lam q1 n1 bod, CheckL (Pi q2 n2 inT outT)) | q1 == q2 → checkDepLam q1 (n1 <|> n2) bod inT outT
  (term, CheckL (Pi QEra _ xTy yT)) → do
    xTy' ← fetchT xTy
    scopedUniVar (const pure) xTy' \uni →
      infer (Term term) . Check =<< (`applyLambda` uni) =<< fetchLambda yT
  (Lam QNorm n bod, InferL) →
    scopedExVar id (Term $ Builtin Any') $ dyn >=> \inT → do
      outT ← fetchT inT >>= \inT' → scopedVar id (QNorm, n, Nothing, inT') $ infer (unLambda bod) Infer
      fetchT inT <&> \inT' → Term $ Pi QNorm Nothing inT' $ Lambda $ nested outT
  (AppErased f a, InferL) → inferApp QEra f a
  (App (unTerm → App (unTerm → Builtin RecordGet) tag) record, mode) → do
    infer tag $ Check $ Term $ Builtin Tag
    tag' ← normalize tag
    let
      mapTerm ∷ (Term → m Term) → a → m a
      cont ∷ Term → m a
      (mapTerm, cont) = case mode of
        (_, Infer) → (id, pure)
        (e, Check ty2) → (const pure, \ty → subtype ty =<< fetchT (Dyn e ty2))
    row0 ← infer record Infer
    res ←
      rowGet
        mapTerm
        tag'
        cont
        row0
        record
    case res of
      LookupFound x → pure x
      LookupMissing d →
        for d fetchT >>= \d' → stackError \p →
          "Couldn't find field" <+> p tag' <+> "among" <+> list (p <$> toList d')
      LookupUnknown → stackError \_ → "Can't check if tag is equal"
  (App f a, InferL) → inferApp QNorm f a
  (FieldsLit (FRecord ()) flds, InferL) → do
    rowFields ← for flds \(n, v) → do
      infer n $ Check $ Term $ Builtin Tag
      vTy ← infer v Infer
      pure (n, vTy)
    pure $ Term $ FieldsLit (FRow ()) rowFields
  (ListLit (Vector' values), (e, Check (Term (App (Term (Builtin List)) (Dyn e → ty))))) → checkList values ty
  (ListLit (Vector' values), (_, Infer)) → Term . App (Term $ Builtin List) . fromMaybe (Term $ Builtin Never) <$> inferList values
  (Concat l (FRecord r), (_, Infer)) →
    Term
      <$> ( Concat
              <$> infer l Infer
              <*> (FRow . (Nothing,) . Lambda . nested <$> infer r Infer)
          )
  (Concat l (FRecord r), CheckL (Concat lT (FRow (_, rT)))) → do
    infer l . Check =<< fetchT lT
    l' ← normalize l
    infer r . Check =<< (`applyLambda` l') =<< fetchLambda rT
  (NumLit x, CheckL (Builtin (Num d))) →
    if x `numFitsInto` d
      then pure ()
      else stackError \_ → "Number literal " <> pretty x <> " does not fit into " <> pIdent (identOfBuiltin $ Num d)
  (NumLit x, InferL) →
    pure
      $ Term
      $ Builtin
      $ Num
      $ let candidates = NumDesc False <$> [Bits8, Bits16, Bits32, Bits64]
         in fromMaybe (NumDesc False BitsInf) $ find @[] (x `numFitsInto`) candidates
  (TagLit _, InferL) → pure $ Term $ Builtin Tag
  (BoolLit _, InferL) → pure $ Term $ Builtin Bool
  (Var i, InferL) → do
    Scopes binds _ _ ← get @Scopes
    let scope = length binds - i - 1
    case binds !? scope of
      Just (QNorm, _, _, ty) → do
        stackLog \p → "var" <+> pretty i <+> ":" <+> p ty
        nestBinding scope ty
      _ → stackError \_ → "Unknown var #" <> pretty i
  -- Type-level
  (FieldsLit (FRow ()) (Vector' flds), InferL) → do
    for_ flds \(n, _) → infer n $ Check $ Term $ Builtin Tag
    inferList (snd <$> flds) >>= withMonoUniverse id (pure . rowOf) . fromMaybe typ
  (FieldsLit (FRow ()) (Vector' flds), (e, Check (unTerm → App (isTypePlus → True) (Dyn e . typOf → ty)))) → do
    for_ flds \(n, _) → infer n $ Check $ Term $ Builtin Tag
    checkList (snd <$> flds) ty
  -- TODO Ctrl+C & Ctrl+V hell, rewrite somehow..
  (Concat l (FRow (i, r)), (e, Check (unTerm → App (isTypePlus → True) (Dyn e → u)))) → do
    infer l . Check . rowOf =<< fetchT u
    l' ← normalize l
    fetchT u
      >>= scopedVar (const pure) (QNorm, i, Nothing, l')
      . infer (unLambda r)
      . Check
      . rowOf
      . nested
  (Concat l (FRow (i, r)), InferL) → do
    infer l Infer
      >>= withMono
        id
        (rowOf <$> subExVar (Term $ Builtin Any'))
        ( \t0 →
            getEpoch >>= \e → case unTerm t0 of
              App (unTerm → Builtin RowPlus) (Dyn e → lT) → do
                l' ← normalize l
                fetchT lT >>= scopedVar (const pure) (QNorm, i, Nothing, l') . infer (unLambda r) . Check . rowOf . nested
                rowOf <$> fetchT lT
              _ → stackError \p → p l <+> "is not a row"
        )
  (Pi _q i inTy outTy, (e, Check (unTerm → App (isTypePlus → True) (Dyn e → u)))) → do
    infer inTy . Check . typOf =<< fetchT u
    inTy' ← normalize inTy
    fetchT u
      >>= scopedVar (const pure) (QNorm, i, Nothing, inTy')
      . infer (unLambda outTy)
      . Check
      . typOf
      . nested
  (Pi _q i inTy outTy, InferL) → do
    infer inTy Infer
      >>= withMonoUniverse
        id
        ( dyn >=> \u → do
            inTy' ← normalize inTy
            fetchT u >>= scopedVar (const pure) (QNorm, i, Nothing, inTy') . infer (unLambda outTy) . Check . typOf . nested
            typOf <$> fetchT u
        )
  (Builtin x, InferL) → pure $ typOfBuiltin x
  (BuiltinsVar, InferL) →
    pure
      $ Term
      $ FieldsLit (FRow ())
      $ Vector'
      $ (\b → (Term $ TagLit $ identOfBuiltin b, typOfBuiltin b))
      <$> builtinsList
  (UniVar _ ty, InferL) → pure ty
  (ExVar (scopeid, subid), InferL) → do
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
  (Sorry, (_, Check k)) → stackLog \p → annotate (color Yellow) $ "sorry :" <+> p k
  (t, (_, Infer)) → stackError \p → p $ Term t
  (t, (e, Check c)) → stackScope (\p → "check via infer" <+> p (Term t) <+> ":" <+> p c) do
    ty ← infer (Term t) Infer
    (ty `subtype`) =<< fetchT (Dyn e c)

typOfBuiltin ∷ BuiltinT → Term
typOfBuiltin = \case
  Num _d → [termQQ| Type^ 0 |]
  Add d → op2d d
  Mul d → op2d d
  IntNeg d → opd d
  Tag → [termQQ| Type^ 0 |]
  Bool → [termQQ| Type^ 0 |]
  RowPlus → [termQQ| Fun (u : Int+) -> Type^ u |]
  List → [termQQ| Fun {u} (Type^ u) -> Type^ u |]
  TypePlus → [termQQ| Fun (u : Int+) -> Type^ (u + 1) |]
  Eq → [termQQ| Fun (Any) (Any) -> Type^ 0 |]
  Refl → [termQQ| Fun {x} -> Eq x x |]
  RecordGet →
    [termQQ|
      Fun {u : Int+} {row : Row^ u} {T : Type^ u} (tag : Tag) (record : {( (tag) = T )} \/ row) -> T
    |]
  -- TODO: Better type
  RecordKeepFields → [termQQ| Fun {u : Int+} {row : Row^ u} (List Tag) (row) -> Any |]
  RecordDropFields → [termQQ| Fun {u : Int+} {row : Row^ u} (List Tag) (row) -> Any |]
  ListLength → [termQQ| Fun {A} (List A) -> Int+ |]
  ListIndexL → [termQQ| Fun {A} (i : Int+) (l : List A) {_ : Where (int_>=0 (int_add (list_length l) (int_neg (i + 1))))} -> A |]
  NatFold → [termQQ| Fun {Acc : Fun (Int+) -> Any} (Acc 0) (Fun (i : Int+) (Acc i) -> Acc (i + 1)) (n : Int+) -> Acc n |]
  If → [termQQ| Fun {A} (cond : Bool) (Fun {_ : Eq cond true} -> A) (Fun {_ : Eq cond false} -> A) -> A |]
  IntGte0 → [termQQ| Fun (Int) -> Bool |]
  IntEq → [termQQ| Fun (Int) (Int) -> Bool |]
  TagEq → [termQQ| Fun (Tag) (Tag) -> Bool |]
  W → [termQQ| Fun {u} (Type^ u) -> Type^ u |]
  Wrap → [termQQ| Fun {A} (A) -> W A |]
  Unwrap → [termQQ| Fun {A} (W A) -> A |]
  Never → [termQQ| Type^ 0 |]
  Any' → [termQQ| Type^ 0 |] where
 where
  opd d = Term $ Pi QNorm Nothing (Term $ Builtin $ Num d) $ Lambda $ Term $ Builtin $ Num d
  op2d d = Term $ Pi QNorm Nothing (Term $ Builtin $ Num d) $ Lambda $ opd d

instMeta ∷ ∀ sig m. (Has Checker sig m) ⇒ (Int, Int) → Term → m ()
instMeta = (\f a b → stackScope (\_ → "instMeta") $ f a b) \(scope1, sub1) →
  let
    getCurrPos (scopeI, subI) = do
      Scopes _ exs _ ← get @Scopes
      pure $ (scopeI,) $ fromMaybe (error "Ex not found in scope") do
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
      getEpoch >>= \e → case t0 of
        (fDyn e → ExVar (scope2, sub2)) → do
          (pos1, pos2) ← (,) <$> getCurrPos (scope1, sub1) <*> getCurrPos (scope2, sub2)
          if pos2 <= pos1
            then pure $ Term $ ExVar (scope2, sub2)
            else do
              u ← fresh
              Scopes _ exs _ ← get @Scopes
              let
                t2 = fromMaybe (error "Ex not found in scope") do
                  (_, scope) ← exs !? fst pos2
                  EVar _ (Right ty) ← scope !? snd pos2
                  pure ty
              writeExBefore [(u, t2)] pos1
              writeMeta (scope2, sub2) (locs, Term $ ExVar (scope1, u))
              pure $ Term $ ExVar (scope1, u)
        uni@(fDyn e → UniVar uni2 _) → do
          (pos1, pos2) ← (,) <$> getCurrPos (scope1, sub1) <*> getCurrPos uni2
          if pos2 <= pos1
            then pure uni
            else stackError \_ → "Attempting to assign existential to later introduced universal"
        Term (App (Term (Builtin W)) a) → pure $ Term $ Term (Builtin W) `App` a
        (fDyn e → App f a) → do
          f' ← instMeta' locs =<< fetchT f
          a' ← instMeta' locs =<< fetchT a
          pure $ Term $ App f' a'
        (fDyn e → FieldsLit fi flds) → Term . FieldsLit fi <$> traverse (bitraverse (instMeta' locs <=< fetchT) (instMeta' locs <=< fetchT)) flds
        (fDyn e → Concat a (FRecord b)) →
          Term
            <$> ( Concat
                    <$> (instMeta' locs =<< fetchT a)
                    <*> (FRecord <$> (instMeta' locs =<< fetchT b))
                )
        (fDyn e → Concat a (FRow (i, b))) → do
          a' ← instMeta' locs =<< fetchT a
          b' ← instMeta' (locs + 1) . unLambda =<< fetchLambda b -- resolve' 1 exs $ unLambda b
          pure $ Term $ Concat a' $ FRow (i, Lambda b')
        (fDyn e → Var x) → pure $ Term $ Var x -- TODO: I hope this is correct, but needs to be rechecked.
        (fDyn e → Builtin x) → pure $ Term $ Builtin x
        (fDyn e → BoolLit x) → pure $ Term $ BoolLit x
        (fDyn e → NumLit x) → pure $ Term $ NumLit x
        (fDyn e → TagLit x) → pure $ Term $ TagLit x
        (fDyn e → Pi QNorm n inT outT) → do
          inT' ← instMeta' locs =<< fetchT inT
          outT' ← instMeta' (locs + 1) . unLambda =<< fetchLambda outT
          pure $ Term $ Pi QNorm n inT' $ Lambda outT'
        x → stackError \p → "instMeta (of" <+> pretty (scope1, sub1) <> ")" <+> p x
   in
    \val →
      let r = writeMeta (scope1, sub1) . (0,) =<< instMeta' 0 val
       in case val of
            Term (ExVar var2) →
              unless ((scope1, sub1) == var2) r
            _ → r

isEqUnify ∷ (Has Checker sig m) ⇒ Term → Term → m EqRes
isEqUnify = isEq' instMeta

-- -- TODO: Use isEq.

-- -- | a <: b Check if type `a` is a subtype of type `b`.
subtype ∷ ∀ sig m. (Has Checker sig m) ⇒ Term → Term → m ()
subtype = \a b →
  stackScope (\p → p a <+> annotate (color Cyan) "<:" <+> p b) $ subtype' a b
 where
  -- Core subtyping logic based on the structure of the resolved types.
  subtype' ∷ Term → Term → m ()
  subtype' t10 t20 =
    getEpoch >>= \e → case (t10, t20) of
      -- Existential Variables (?a <: ?b, ?a <: T, T <: ?a)
      (fDyn e → ExVar ex1, fDyn e → ExVar ex2) | ex1 == ex2 → pure ()
      (fDyn e → ExVar ex1, t2) → instMeta ex1 t2
      (t1, fDyn e → ExVar ex) → instMeta ex t1
      -- Universal Variables (u1 <: u2) - Must be identical.
      (fDyn e → UniVar id1 _, fDyn e → UniVar id2 _) | id1 == id2 → pure ()
      -- T <: Pi QEra x:K. Body  => Introduce UniVar for x
      (t, unTerm → Pi QEra (Just _n) inT outT) →
        scopedUniVar (const pure) inT (subtype t <=< applyLambda outT)
      -- Pi QEra x:K. Body <: T => Introduce ExVar for x
      (unTerm → Pi QEra (Just n) inT outT, t) →
        scopedExVar (\_ _ → stackError \_ → "Unresolved existential" <+> pIdent n) inT ((`subtype` t) <=< applyLambda outT)
      -- Function Types (Πx:T1.U1 <: Πy:T2.U2)
      (fDyn e → Pi q1 n1 inT1 outT1, fDyn e → Pi q2 n2 inT2 outT2) | q1 == q2 → do
        -- Input types are contravariant (T2 <: T1)
        uncurry subtype =<< (,) <$> fetchT inT2 <*> fetchT inT1
        -- Output types are covariant
        fetchT inT2 >>= \inT2' → scopedVar (const pure) (QNorm, n1 <|> n2, Nothing, inT2') do
          outT1' ← fetchLambda outT1
          outT2' ← fetchLambda outT2
          subtype (unLambda outT1') (unLambda outT2')
      (fDyn e → Builtin (Num d1@(NumDesc nonneg1 bits1)), fDyn e → Builtin (Num d2@(NumDesc nonneg2 bits2))) →
        let fits = case (nonneg1, nonneg2) of
              (True, False) → bits1 < bits2 || bits2 == BitsInf
              (False, True) → False
              _ → bits1 <= bits2
         in if fits then pure () else stackError \_ → "Cannot fit " <> pIdent (identOfBuiltin $ Num d1) <> " into " <> pIdent (identOfBuiltin $ Num d2)
      (fDyn e → Builtin Never, _) → pure ()
      (_, fDyn e → Builtin Any') → pure ()
      -- Builtin Types (must be identical)
      (fDyn e → Builtin a, fDyn e → Builtin b) | a == b → pure ()
      (fDyn e → Var i, fDyn e → Var j) | i == j → pure ()
      -- Type Universes (Type L1 <: Type L2 where L1 <= L2)
      (Term (App (fDyn e → Builtin TypePlus) a0), Term (App (fDyn e → Builtin TypePlus) b0)) → do
        case (a0, b0) of
          (fDyn e → NumLit 0, _) → pure ()
          -- If one level is existential, unify it with the other level constraint.
          (fDyn e → ExVar ex, b) → instMeta ex b
          (a, fDyn e → ExVar ex) → instMeta ex a
          (a, b) →
            isEqUnify a b >>= \case
              -- Skippind `dyn`'s here since non-EqYes doesn't update a & b.
              EqYes → pure ()
              _ → do
                let negA = Term $ Term (Builtin $ IntNeg IntND) `App` a
                evaluated ← normalize (Term $ Term (Builtin IntGte0) `App` Term (Op2 (Add IntND) b negA))
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
      (fDyn e → FieldsLit (FRow ()) (Vector' fields1), fDyn e → FieldsLit (FRow ()) fields2) →
        foldM_
          ( \fields1' (tag, ty) →
              ifoldr
                ( \i (tag2, ty2) rec →
                    ((,) <$> fetchT tag <*> fetchT tag2) >>= uncurry isEqUnify >>= \case
                      EqYes → do
                        uncurry subtype =<< ((,) <$> fetchT ty <*> fetchT ty2)
                        pure $ deleteAt i fields1'
                      EqUnknown →
                        fetchT tag >>= \tag' →
                          fetchT tag2 >>= \tag2' →
                            stackError \p → "Unable to check field equality when subtyping:" <+> p tag' <+> "?=" <+> p tag2'
                      EqNot → rec
                )
                (fetchT tag >>= \tag' → fetchT ty >>= \ty' → stackError \p → "Can't find" <+> p tag' <+> "in" <+> p ty')
                fields1'
          )
          fields1
          fields2
      -- n : l1 \/ r1  <:  n : l2 \/ r2
      (fDyn e → Concat l1 (FRow (n1, lr1)), fDyn e → Concat l2 (FRow (n2, lr2))) → do
        uncurry subtype =<< ((,) <$> fetchT l1 <*> fetchT l2)
        fetchT l1 >>= \l1' → scopedVar (const pure) (QNorm, n1 <|> n2, Nothing, l1') do
          body1' ← fetchLambda lr1
          body2' ← fetchLambda lr2
          subtype (unLambda body1') (unLambda body2')
      -- Catch-all: if no rule matches, check equality
      (t1, t2) →
        isEqUnify t1 t2 >>= \case
          EqYes → pure ()
          _ → stackError \p → "Subtype check failed, no rule applies for:" <+> p t1 <+> "<:" <+> p t2

runChecker' ∷ (Applicative m) ⇒ FreshC (ErrorC e (StateC Scopes m)) a → m (Either e a)
runChecker' =
  runContext'
    . runError (pure . Left) (pure . Right)
    . evalFresh 0

checkSource ∷ ByteString → IO ()
checkSource source = do
  term ← either (fail . show) pure $ parse [] source
  (stacks, res) ← runIsolate $ runStackAccC $ runChecker' $ infer term Infer
  render case res of
    Left e →
      pStacks stacks
        <> line
        <> annotate (color Red) "error: "
        <> e
    Right r → pTerm [] r

checkSourceDebug ∷ ByteString → IO ()
checkSourceDebug source = do
  term ← either (fail . show) pure $ parse [] source
  res ← runIsolate $ runStackPrintC $ runChecker' $ infer term Infer
  render case res of
    Left e → annotate (color Red) "error: " <> e
    Right r → pTerm [] r

checkFile ∷ FilePath → IO ()
checkFile file = checkSource =<< readFileBinary file

checkFileDebug ∷ FilePath → IO ()
checkFileDebug file = checkSourceDebug =<< readFileBinary file

main ∷ IO ()
main = pure ()
