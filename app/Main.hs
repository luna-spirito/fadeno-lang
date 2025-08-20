module Main where

import Control.Algebra
import Control.Carrier.Error.Church (ErrorC, runError)
import Control.Carrier.Fresh.Church (FreshC, evalFresh)
import Control.Carrier.Reader (ReaderC, runReader)
import Control.Carrier.State.Church (StateC)
import Control.Carrier.Writer.Church (WriterC, execWriter, runWriter)
import Control.Effect.Empty (empty)
import Control.Effect.Error (Error, throwError)
import Control.Effect.Fresh (Fresh, fresh)
import Control.Effect.Lift (Lift, sendIO)
import Control.Effect.Reader (Reader, ask, local)
import Control.Effect.State (State, get, modify, put, state)
import Control.Effect.Throw (Throw)
import Control.Effect.Writer (Writer, censor, listen, tell)
import Data.Bitraversable (bimapM)
import Data.ByteString.Char8 (pack)
import Data.List (find, sortBy)
import Data.RRBVector (Vector, adjust, adjust', deleteAt, drop, findIndexL, ifoldl', ifoldr, splitAt, unzip, viewl, viewr, zip, (!?), (<|), (|>))
import Data.Type.Equality (type (~))
import GHC.Exts (IsList (..))
import Normalize (Binding, Context, Dyn (..), EEntry (..), Epoch (..), EqRes (..), Exs, applyLambda, fetchT, getEpoch, isEq', normalize, numDecDispatch, rewrite, runContext, splitAt3, termQQ, withBinding)
import Parser (Bits (..), BlockF (..), BuiltinT (..), Fields (..), Ident (..), Lambda (..), NumDesc (..), Quant (..), Term (..), TermF (..), Vector' (..), builtinsList, identOfBuiltin, intercept, nested, nestedBy', nestedByP, pIdent, pQuant, pTerm, parse, render, rowOf, traverseTermF, typOf)
import Prettyprinter (Doc, annotate, group, indent, line, nest, pretty, (<+>))
import Prettyprinter.Render.Terminal (AnsiStyle, Color (..), color)
import RIO hiding (Reader, Vector, ask, concat, drop, filter, link, local, runReader, toList, zip)
import RIO.HashMap qualified as HM

-- TODO: You currently don't perform `resolve` in terms processed...
-- This is probably an error.

-- TODO: Permit inference of dependent Pis?
-- TODO: Recheck the whole file.
-- TODO: Concat uncomfortably replicate Pi.
-- TODO: errors. Probably all impossibles as `error` or `undefined`

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
termLoggerM = (\ctx → pTerm $ (\(q, n, _, _) → (q, n)) <$> ctx) <$> get @(Vector Binding)

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

-- writeMeta' ∷ ∀ sig m. (Has Checker sig m) ⇒ (Int, Int) → Term → m ()
-- writeMeta' = \(scope, subi) val → do
--   exs0 ← get @Exs
--   let (exsBefore, exsMiddleM, exsAfter) = splitAt3 scope exs0
--   (exsMiddleBef, exMiddleMiddle, exsMiddleAft) ← maybe (stackError \_ → "Internal error: ex not found in context") pure do
--     middle ← exsMiddleM
--     i ← findIndexL ((== subi) . fst) middle
--     pure $ splitAt3 i middle
--   case exMiddleMiddle of
--     Just (Right _) → _
--   (bindsBefore, bindsAfter) ← splitAt scope <$> get @(Vector Binding)
--   put $ exsBefore |> (exsMiddleBef |> (subi, Left val))
--   put bindsBefore
--   let
--     fe ∷ (Int, Either Term Term) → m ()
--     fe (exId, valty) = do
--       valty' ← bimapM f f valty
--       modify @Exs \exs → adjust' (length exs - 1) (|> (exId, valty')) exs
--     fb (q, n, val, ty) = do
--       ty' ← f ty
--       modify @(Vector Binding) (|> (q, n, val, ty'))
--   for_ exsMiddleAft fe
--   for_ (zip bindsAfter exsAfter) \(b, e) → do
--     fb b
--     modify @Exs (|> [])
--     for_ e fe

writeMeta ∷ ∀ sig m. (Has Checker sig m) ⇒ (Int, Int) → Term → m ()
writeMeta exId0@(scope0, subi0) valNow0 = do
  stackLog \p → "exi# " <> pretty exId0 <+> ":=" <+> p valNow0
  binds ← get @(Vector Binding)
  let depth = length binds - scope0 -- no -1 due to scope being ridiculous
  val0 ← maybe (stackError \_ → "Leak") pure $ nestedBy' valNow0 $ -depth
  exs0 ← get @Exs
  let (exsBefore, exsMiddleM, exsAfter) = splitAt3 scope0 exs0
  (Epoch exsMiddleEpoch, (exsMiddleBef, exsMiddleMiddle, exsMiddleAft)) ← maybe (stackError \_ → "ex not found in context") pure do
    middle ← exsMiddleM
    i ←
      findIndexL
        ( \case
            EVar subi2 _ → subi2 == subi0
            EMarker → False
        )
        $ snd middle
    pure $ splitAt3 i <$> middle
  put $ exsBefore |> (Epoch $ exsMiddleEpoch + 1, exsMiddleBef)
  case exsMiddleMiddle of
    Just (EVar _ (Right ty)) → infer val0 $ Check ty
    _ → stackError \_ → "Internal error: existential already instantiated"
  (bindsBefore, bindsAfter) ← splitAt scope0 <$> get @(Vector Binding)
  put $ exsBefore |> (Epoch $ exsMiddleEpoch + 1, exsMiddleBef |> EVar subi0 (Left val0))
  put bindsBefore
  let
    fe ∷ EEntry → m ()
    fe = \case
      EMarker → modify @Exs \exs → adjust (length exs - 1) (fmap (|> EMarker)) exs
      EVar exId valty → do
        valty' ← bimapM normalize normalize valty
        modify @Exs \exs → adjust' (length exs - 1) (fmap (|> EVar exId valty')) exs
    fb (q, n, val, ty) = do
      ty' ← normalize ty
      modify @(Vector Binding) (|> (q, n, val, ty'))
  for_ exsMiddleAft fe
  for_ (zip bindsAfter exsAfter) \(b, (Epoch epoch, e)) → do
    fb b
    modify @Exs (|> (Epoch $ epoch + 1, []))
    for_ e fe

-- -- TODO: Dependent.

-- | Introduce new variable/binding.
scopedVar ∷ (Has Checker sig m) ⇒ ((Term → m Term) → a → m a) → (Quant, Maybe Ident, Maybe Term, Term) → m a → m a
scopedVar mapTerm (bindQ, bindI, bindT, bindTy) act =
  withBinding (bindQ, bindI, bindT, bindTy) act
    >>= mapTerm (\t → maybe (stackError \p → "Var leaked in" <+> p t) pure $ nestedBy' t $ -1)

scopedUniVar ∷ (Has Checker sig m) ⇒ ((Term → m Term) → a → m a) → (TermF Term → m a) → m a
scopedUniVar mapTerm act = do
  uni1 ← fresh
  let ensureNotOcc = fix \rec →
        unTerm >>> fmap Term . \case
          UniVar uni2 | uni1 == uni2 → stackError \_ → "UniVar leaked"
          x → traverseTermF rec (fmap Lambda . rec . unLambda) x
  act (UniVar uni1) >>= mapTerm ensureNotOcc

freshIdent ∷ (Has Fresh sig m) ⇒ m Ident
freshIdent = (`Ident` False) . ("/" <>) . pack . show <$> fresh

scopedExVar ∷ (Has Checker sig m) ⇒ ((Term → m Term) → a → m a) → Term → (Dyn → m a) → m a
scopedExVar mapTerm ty0 act = do
  scopeId ← (\x → x - 1) . length <$> get @Exs
  sub ← fresh
  modify @Exs $ adjust' scopeId (fmap (<> [EMarker, EVar sub (Right ty0)]))
  res ← act =<< (`Dyn` Term (ExVar (scopeId, sub))) <$> getEpoch
  unresolved ← state @Exs \scopes →
    let
      (scopesB, (scopeE, scope)) = fromMaybe (error "Missing ex scope") $ viewr scopes
      (scope', unresolved) =
        fix
          ( \rec →
              viewr >>> \case
                Nothing → error "Marker disappeared"
                Just (rest, EMarker) → (rest, [])
                Just (rest, EVar _ (Left _)) → rec rest
                Just (rest, EVar i (Right ty)) → (|> (i, ty)) <$> rec rest
          )
          scope
     in
      (scopesB |> (scopeE, scope'), unresolved)
  -- TODO: occurence check?
  mapTerm
    ( \t →
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
                        x → traverseTermF (rec) (fmap Lambda . local @Int (+ 1) . rec . unLambda) x
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

writeExBefore ∷ (Has Context sig m) ⇒ Vector (Int, Term) → (Int, Int) → m ()
writeExBefore entries (scopeI, beforeSub) = modify @Exs $ adjust' scopeI $ fmap \scope →
  let (before, after) =
        splitAt
          ( fromMaybe (error "Ex not found in context")
              $ findIndexL
                ( \case
                    EMarker → False
                    EVar sub _ → beforeSub == sub
                )
                scope
          )
          scope
   in before <> fmap (\(i, t) → EVar i $ Right t) entries <> after

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
        writeMeta (scope, sub) res
        onOther res
      Pi QEra _n x y | foralls → stackScope (\_ → "(unwrapped forall)")
        $ scopedExVar mapTerm x \ex → fetchT ex >>= \ex' → go $ applyLambda y ex'
      r → onOther $ Term r

withMono ∷
  (Has Checker sig m) ⇒
  ((Term → m Term) → a → m a) →
  ReaderC Int (WriterC (Vector (Int, Term)) m) Term →
  (Term → m a) →
  Term →
  m a
withMono = withMono' True

-- isEqUnify ∷ (Has Checker sig m) ⇒ Term → Term → m EqRes
-- isEqUnify = isEq' instMeta

data LookupRes a
  = LookupFound !a
  | LookupMissing !(Vector' Term) -- Visited keys
  | LookupUnknown
  deriving (Show)

-- {- | Accepts `tag`, `row` and `record`. Provides access to the field `tag` in `row`,
-- performs refines if necessary.
-- -}
-- rowGet ∷ ∀ sig m a. (Has Solve sig m) ⇒ ((Term → m Term) → a → m a) → Term → (Term → m a) → Term → Term → m (LookupRes a)
-- rowGet mapTerm tag cont = go
--  where
--   notARow x = stackError \p → "Not a row:" <+> p x
--   go ∷ Term → Term → m (LookupRes a)
--   go row record =
--     withMono
--       ( \f → \case
--           LookupFound a → LookupFound <$> mapTerm f a
--           LookupMissing (Vector' keys) → LookupMissing . Vector' <$> traverse f keys
--           LookupUnknown → pure LookupUnknown
--       )
--       ( do
--           (tName, tId) ← subExVar' "t"
--           local (\_ → (tName, tId, Builtin Any')) do
--             let t = ExVar tName tId $ Builtin Any'
--             tail ← subExVar "tail" $ rowOf $ nested t
--             pure $ Concat (FieldsLit (FRow ()) [(tag, t)]) (FRow (Nothing, Lambda tail))
--       )
--       ( \_ → \case
--           FieldsLit (FRow ()) (Vector' l) → case viewl l of
--             Nothing → pure $ LookupMissing []
--             Just ((n, v), rest) → runSeqResolve do
--               eqTag ← withResolved \_ → isEqUnify n tag
--               case eqTag of
--                 EqYes → LookupFound <$> withResolved \exs → cont (resolve exs v)
--                 EqNot → do
--                   inRest ← withResolved \exs → go (FieldsLit (FRow ()) (Vector' $ bimap (resolve exs) (resolve exs) <$> rest)) record
--                   case inRest of
--                     LookupFound res → pure $ LookupFound res
--                     LookupMissing (Vector' fi) → withResolved \exs → pure $ LookupMissing $ Vector' $ resolve exs n <| fi
--                     LookupUnknown → pure LookupUnknown
--                 EqUnknown → pure LookupUnknown
--           Concat l (FRow (_, r)) → runSeqResolve do
--             inL ← withResolved \exs → go (resolve exs l) record
--             case inL of
--               LookupMissing visited1 → do
--                 let
--                   select f = normalize [] $ App (App (Builtin f) $ ListLit $ visited1) record
--                   recordL = select RecordKeepFields
--                   recordR = select RecordDropFields
--                 r' ← withResolved \exs → go (resolve exs $ applyLambda r recordL) recordR
--                 case r' of
--                   LookupMissing visited2 → pure $ LookupMissing $ visited1 <> visited2
--                   o → pure o
--               o → pure o
--           x → notARow x
--       )
--       row

-- unifyFields ∷ (Has Solve sig m) ⇒ Vector' (Term, Term) → StateC (Maybe Term) m ()
-- unifyFields fi = runSeqResolve $ for_ fi \(_fieldName, fieldValue) → do
--   fieldValue' ← withResolved \exs → pure $ resolve exs fieldValue
--   currentUnifiedTyM ← get
--   withResolved \_ → case currentUnifiedTyM of
--     Nothing → put $ Just fieldValue'
--     Just currentUnifiedTy → runSeqResolve do
--       withResolved \_ → subtype fieldValue' currentUnifiedTy
--       withResolved \exs → put $ Just $ resolve exs currentUnifiedTy

-- -- TODO: Just remove this... please...
-- ensureIsType ∷ (Has Solve sig m) ⇒ Term → m Term
-- ensureIsType t =
--   withMono
--     id
--     (lift fails)
--     ( \_ → \ty → case ty of
--         App (Builtin TypePlus) _ → pure ty
--         App (Builtin Row) _ → pure ty
--         -- Currently ensureIsType is used in writeMeta for ExSuperType. So don't uncomment this without thinking!
--         -- App (Builtin Row) _ → pure ty
--         -- App (Builtin Record) r →
--         --   rowOf <$> withKnownFields id r \fields →
--         --     fromMaybe bottomRow <$> execState Nothing (unifyFields fields)
--         _ → fails
--     )
--     t
--  where
--   fails = stackError \p → p t <> " is not a type?"

-- nestMode ∷ InferMode a → InferMode a
-- nestMode = \case
--   Infer → Infer
--   Check x → Check $ nested x

-- -- TODO: We could implement "bindings update" as an effect.
-- -- Performance improvements over rewriting all the bindings.

-- resolveBinds ∷ Resolved → Vector (Quant, Maybe Term, Term) → Vector (Quant, Maybe Term, Term)
-- resolveBinds (HM.null → True) = id
-- resolveBinds exs = fmap $ bimap id $ resolve exs

-- resolveMode ∷ Resolved → InferMode a → InferMode a
-- resolveMode exs = \case
--   Infer → Infer
--   Check a → Check $ resolve exs a

-- -- | Select bindings for normalizing annotations.
-- annoBinds ∷ (Has Solve sig m) ⇒ m (Vector (Maybe Term))
-- annoBinds = (fmap \(_, _, a, _) → a) <$> ask @(Vector Binding)

-- -- | Select bindings for normalizing terms.
-- termBinds ∷ (Has Solve sig m) ⇒ m (Vector (Maybe Term))
-- termBinds =
--   let f = \(q, _, a, _) → case q of
--         QEra → Just undefined -- Just and not Nothing to make sure `normalize` erases it.
--         QNorm → a
--    in (fmap f) <$> ask @(Vector Binding)

-- checkDepLam ∷ ∀ sig m. (Has Solve sig m) ⇒ Quant → Maybe Ident → Lambda Term → Term → Lambda Term → m ()
-- checkDepLam q i bod inT outT =
--   scopedVar (const pure) (q, i, Nothing, inT)
--     $ infer (unLambda bod)
--     $ Check
--     $ unLambda outT

-- inferApp ∷ (Has Solve sig m) ⇒ Quant → Term → Term → m Term
-- inferApp q f a = runSeqResolve do
--   let norm = q == QNorm
--   fTy ← withResolved \_ → infer f Infer
--   withResolved \_ →
--     withMono'
--       norm
--       id
--       ( if norm
--           then Pi QNorm Nothing <$> subExVar "in" (Builtin Any') <*> (Lambda <$> subExVar "out" (Builtin Any'))
--           else stackError \_ → "Cannot apply erased argument to unknown"
--       )
--       ( \_ → \case
--           Pi q2 _n inT outT | q == q2 → runSeqResolve do
--             let updCtx = if norm then id else local @(Vector Binding) ((\(_, i, t, ty) → (QNorm, i, t, ty)) <$>)
--             withResolved \_ → updCtx $ infer a $ Check $ inT
--             withResolved \exs → do
--               ab ← annoBinds
--               pure $ resolve exs $ applyLambda outT (normalize ab a)
--           t → stackError \p → "inferApp" <+> pretty (show q) <+> p t
--       )
--       fTy

-- checkList ∷ (Has Solve sig m) ⇒ Vector Term → Term → m Term
-- checkList = flip $ foldM \ty0 v → runSeqResolve do
--   withResolved \_ → infer v $ Check ty0
--   withResolved \exs → pure $ resolve exs ty0

-- inferList ∷ (Has Solve sig m) ⇒ Vector Term → m (Maybe Term)
-- inferList tts = for (viewl tts) \(t, ts) → runSeqResolve do
--   tT ← withResolved \_ → infer t Infer
--   withResolved \_ → checkList ts tT

data InferMode a where
  Infer ∷ InferMode Term
  Check ∷ Term → InferMode ()

{- | Left is original, right is dynamic. This is absolutely ugly, but necessary for some of the cases, where left is needed.
unwrapMode :: Has Context sig m ⇒ InferMode Term a → m (InferMode (Dyn, TermF Dyn) a)
unwrapMode = \case
  Infer → pure Infer
  Check c → Check <$> ((,) <$> dyn c <*> unwrap c) -- 💀
{\-# INLINE unwrapMode #-\}
-}

--

logAndRunInfer ∷ ∀ sig m a. (Has Checker sig m) ⇒ ((TermF Term, (Epoch, InferMode a)) → m a) → Term → InferMode a → m a
logAndRunInfer f t mode =
  let act = getEpoch >>= \e → f (unTerm t, (e, mode))
   in case t of
        Term Block{} → act -- No logging to reduce noise
        _ →
          let
            scope x = stackScope @sig @m @a \p → ("<" <> group (p t) <> "> : " <> x p)
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

-- insideEra ∷ Vector Binding → Vector Binding
-- insideEra = fmap \(_q, a, b, c) → (QNorm, a, b, c)

withEra ∷ (Has (State (Vector Binding)) sig m) ⇒ m a → m a
withEra act = do
  quants ← state @(Vector Binding) \binds →
    unzip ((\(q, a, b, c) → ((QNorm, a, b, c), q)) <$> binds)
  res ← act
  modify @(Vector Binding) \binds →
    (\(q, (_, a, b, c)) → (q, a, b, c)) <$> zip quants binds
  pure res

-- mapTermFor ∷ (Applicative f) ⇒ InferMode a → ((Term → f Term) → a → f a)
-- mapTermFor = \case
--   Infer → id
--   Check _ → const pure

-- | Check, instantly unwrapping a layer
pattern CheckL ∷ () ⇒ (a2 ~ ()) ⇒ TermF Dyn → (Epoch, InferMode a2)
pattern CheckL x ← (e, Check (run . traverseTermF (pure . Dyn e) (pure . Lambda . Dyn e . unLambda) . unTerm → x))

pattern InferL ∷ () ⇒ (a2 ~ Term) ⇒ (a1, InferMode a2)
pattern InferL ← (_, Infer)

-- | Either infers a normalized type for the value and context, or checks a value against the normalized type.
infer ∷ ∀ sig m a. (Has Checker sig m) ⇒ Term → InferMode a → m a
infer = logAndRunInfer $ \case
  -- Here, we will convert Checks to Infers.
  -- However, converting Infer to a Check when checking a term is hereby declared a deadly sin.
  (_, CheckL (Builtin Any')) → pure ()
  (Block (BlockLet q name tyM val into), mode) → do
    ty ← stackScope (\_ → ("let" <+> pQuant q <> maybe "_" pIdent name))
      $ (if q == QEra then withEra else id)
      $ case tyM of
        Nothing → infer val Infer
        Just ty → do
          ty' ← normalize ty
          infer val $ Check ty
          pure ty'
    val' ← normalize val
    withBlockLog (unLambda into) $ case mode of
      (_, Infer) → scopedVar id (q, name, Just val', ty) $ infer (unLambda into) Infer
      (e, Check subty0) → do
        subty ← fetchT $ Dyn e subty0
        scopedVar (const pure) (q, name, Just val', ty) $ infer (unLambda into) $ Check $ nested subty
  -- (Block (BlockRewrite prf inner), mode) → runSeqResolve do
  --   -- Currently: Eq <simple/outer> <complicated/inner>
  --   let rewriteTerm' what with x = case rewriteTerm what with x of
  --         Just x' → pure x'
  --         Nothing → stackError \p → "Rewrite" <+> p what <+> "==>" <+> p with <+> "did not alter" <+> p x
  --   prfTy ← withResolved \_ → infer prf Infer
  --   withResolved \_ →
  --     withMono
  --       (mapTermFor mode)
  --       (stackError \_ → "Type of rewrite must be known")
  --       ( \_ → \case
  --           Builtin Eq `App` simple `App` complicated → withBlockLog inner $ case mode of
  --             Infer → runSeqResolve do
  --               innerTy ← withResolved \_ → infer inner Infer
  --               withResolved \exs2 → rewriteTerm' (resolve exs2 complicated) (resolve exs2 simple) innerTy
  --             Check ty → infer inner . Check =<< rewriteTerm' simple complicated ty
  --           x → stackError \p → p x <+> "is invalid rewrite"
  --       )
  --       prfTy
  -- -- TODO: (Lam QEra arg bod, Infer)
  -- (Lam QEra n1 bod, Check (Pi QEra n2 inT outT)) → checkDepLam QEra (n1 <|> n2) bod inT outT
  -- (AppErased f a, Infer) → inferApp QEra f a
  -- (term, Check (Pi QEra n xTy yT)) → do
  --   uniId ← fresh
  --   scopedUniVar (const pure) uniId $ infer term $ Check $ applyLambda yT $ UniVar n uniId xTy
  (Lam QNorm n bod, InferL) → scopedExVar id (Term $ Builtin Any') \inT → do
    outT ← fetchT inT >>= \inT' → scopedVar id (QNorm, n, Nothing, inT') $ infer (unLambda bod) Infer
    fetchT inT <&> \inT' → Term $ Pi QNorm Nothing inT' $ Lambda $ nested outT
  -- (Lam QNorm n1 bod, Check (Pi QNorm n2 inT outT)) → checkDepLam QNorm (n1 <|> n2) bod inT outT
  -- (App (App (Builtin RecordGet) tag) record, mode) → runSeqResolve do
  --   withResolved \_ → infer tag $ Check $ Builtin Tag
  --   row0 ← withResolved \_ → infer record Infer
  --   stackLog \p → p tag <+> p row0 <+> p record
  --   withResolved \_ → do
  --     res ←
  --       rowGet
  --         (mapTermFor mode)
  --         tag
  --         ( \ty → case mode of
  --             Infer → pure ty
  --             Check ty2 → subtype ty ty2
  --         )
  --         row0
  --         record
  --     case res of
  --       LookupFound x → pure x
  --       _ → stackError \_ → "App RecordGet"
  -- (App f a, Infer) → inferApp QNorm f a
  -- (FieldsLit (FRecord ()) flds, Infer) → runSeqResolve do
  --   rowFields ← for flds \(n, v) → do
  --     withResolved \_ → infer n $ Check $ Builtin Tag
  --     vTy ← withResolved \_ → infer v Infer
  --     pure (n, vTy)
  --   pure $ FieldsLit (FRow ()) rowFields
  -- (ListLit (Vector' values), Check (App (Builtin List) ty)) → void $ checkList values ty
  -- (ListLit (Vector' values), Infer) → App (Builtin List) . fromMaybe (Builtin Never) <$> inferList values
  -- (Concat l (FRecord r), Infer) →
  --   runSeqResolve
  --     $ Concat
  --     <$> (withResolved \_ → infer l Infer)
  --     <*> (withResolved \_ → FRow . (Nothing,) . Lambda . nested <$> infer r Infer)
  -- (Concat l (FRecord r), Check (Concat lT (FRow (_, rT)))) → runSeqResolve do
  --   withResolved \_ → infer l $ Check lT
  --   withResolved \exs → do
  --     ab ← termBinds
  --     infer r $ Check $ resolve exs $ applyLambda rT (normalize ab l)
  -- (NumLit x, Check (Builtin (Num d))) →
  --   if x `numFitsInto` d
  --     then pure ()
  --     else stackError \_ → "Number literal " <> pretty x <> " does not fit into " <> pIdent (identOfBuiltin $ Num d)
  -- (NumLit x, Infer) →
  --   pure
  --     $ Builtin
  --     $ Num
  --     $ let candidates = NumDesc False <$> [Bits8, Bits16, Bits32, Bits64]
  --        in fromMaybe (NumDesc False BitsInf) $ find @[] (x `numFitsInto`) candidates
  -- (TagLit _, Infer) → pure $ Builtin Tag
  -- (BoolLit _, Infer) → pure $ Builtin Bool
  (Var i, InferL) → do
    binds ← get @(Vector Binding)
    case binds !? i of
      Just (QNorm, _, _, ty) → do
        stackLog \p → "var" <+> pretty i <+> ":" <+> p ty
        pure $ nestedByP ty i
      _ → stackError \_ → "Unknown var #" <> pretty i
  -- -- Type-level
  -- -- (FieldsLit (FRow ()) flds, Infer) → error "make c
  -- (FieldsLit (FRow ()) (Vector' flds), Infer) → runSeqResolve do
  --   for_ flds \(n, _) → withResolved \_ → infer n $ Check $ Builtin Tag
  --   withResolved \_ → rowOf . fromMaybe (Builtin Never) <$> inferList (snd <$> flds)
  -- (FieldsLit (FRow ()) (Vector' flds), Check (App (Builtin Row) ty)) → runSeqResolve do
  --   for_ flds \(n, _) → withResolved \_ → infer n $ Check $ Builtin Tag
  --   withResolved \exs → void $ checkList (snd <$> flds) $ resolve exs ty
  -- (inp@(FieldsLit (FRow ()) _), Check (App (Builtin TypePlus) u)) → infer inp $ Check $ rowOf $ typOf u -- Lazy redirect
  -- -- TODO Ctrl+C & Ctrl+V hell, rewrite somehow..
  -- (Concat l (FRow (i, r)), Check (App (Builtin Row) ty)) → runSeqResolve do
  --   withResolved \_ → infer l $ Check $ rowOf ty
  --   withResolved \exs → do
  --     ab ← termBinds
  --     scopedVar (const pure) (QNorm, i, Nothing, normalize ab l)
  --       $ infer (unLambda r)
  --       $ Check
  --       $ rowOf
  --       $ nested
  --       $ resolve exs ty
  -- (inp@(Concat _ (FRow _)), Check (App (Builtin TypePlus) u)) → infer inp $ Check $ rowOf $ typOf u -- Lazy redirect
  -- (Concat l (FRow (i, r)), Infer) → runSeqResolve do
  --   lT0 ← withResolved \_ → infer l Infer
  --   withResolved \_ →
  --     withMono
  --       id
  --       (rowOf <$> subExVar "t" (Builtin Any'))
  --       ( \_ → \case
  --           App (Builtin Row) lT → runSeqResolve do
  --             withResolved \_ → do
  --               ab ← termBinds
  --               scopedVar (const pure) (QNorm, i, Nothing, normalize ab l) $ infer (unLambda r) $ Check $ rowOf $ nested lT
  --             withResolved \exs → pure $ rowOf $ resolve exs lT
  --           _ → stackError \p → p l <+> "is not a row"
  --       )
  --       lT0
  -- (Pi _q i inTy outTy, Check (App (Builtin TypePlus) u)) → runSeqResolve do
  --   withResolved \_ → infer inTy $ Check $ typOf u
  --   withResolved \exs → do
  --     ab ← termBinds
  --     scopedVar (const pure) (QNorm, i, Nothing, normalize ab inTy)
  --       $ infer (unLambda outTy)
  --       $ Check
  --       $ typOf
  --       $ nested
  --       $ resolve exs u
  -- (Pi _q i inTy outTy, Infer) → runSeqResolve do
  --   inTyTy0 ← withResolved \_ → infer inTy Infer
  --   withResolved \_ →
  --     withMono
  --       id
  --       (typOf <$> subExVar "u" (Builtin $ Num $ NumDesc True BitsInf))
  --       ( \_ → \case
  --           App (Builtin TypePlus) u → runSeqResolve do
  --             withResolved \_ → do
  --               ab ← annoBinds
  --               scopedVar (const pure) (QNorm, i, Nothing, normalize ab inTy) $ infer (unLambda outTy) $ Check $ typOf $ nested u
  --             withResolved \exs → pure $ rowOf $ resolve exs u
  --           _ → stackError \p → p inTy <+> "is not a type"
  --       )
  --       inTyTy0
  -- (Builtin x, Infer) → pure $ typOfBuiltin x
  -- (BuiltinsVar, Infer) →
  --   pure
  --     $ FieldsLit (FRow ())
  --     $ Vector'
  --     $ (\b → (TagLit $ identOfBuiltin b, typOfBuiltin b))
  --     <$> builtinsList
  -- -- (UniVar _n _i ty, Infer) → pure ty
  -- -- (ExVar _n _i ty, Infer) → pure ty
  -- (Sorry, Check k) → stackLog \p → annotate (color Yellow) $ "sorry :" <+> p k
  (t, InferL) → stackError \p → p $ Term t
  (t, (e, Check c)) → stackScope (\p → "check via infer" <+> p (Term t) <+> ":" <+> p c) do
    ty ← infer (Term t) Infer
    (`subtype` ty) =<< fetchT (Dyn e c)

-- typOfBuiltin ∷ BuiltinT → Term
-- typOfBuiltin = \case
--   Num _d → [termQQ| Type+ 0 |]
--   Add d → op2d d
--   IntNeg d → opd d
--   Tag → [termQQ| Type+ 0 |]
--   Bool → [termQQ| Type+ 0 |]
--   Row → [termQQ| Fun {u} (Type+ u) -> Type+ u |]
--   List → [termQQ| Fun {u} (Type+ u) -> Type+ u |]
--   TypePlus → [termQQ| Fun (u : Int+) -> Type+ (u + 1) |]
--   Eq → [termQQ| Fun (Any) (Any) -> Type+ 0 |]
--   Refl → [termQQ| Fun {x} -> Eq x x |]
--   RecordGet →
--     [termQQ|
--       Fun {K} {row : Row K} {T : K} (tag : Tag) (record : {( (tag) = T )} \/ row) -> T
--     |]
--   -- TODO: Better type
--   RecordKeepFields → [termQQ| Fun {K} {row : Row K} (List Tag) (row) -> Any |]
--   RecordDropFields → [termQQ| Fun {K} {row : Row K} (List Tag) (row) -> Any |]
--   ListLength → [termQQ| Fun {A} (List A) -> Int+ |]
--   ListIndexL → [termQQ| Fun {A} (i : Int+) (l : List A) {_ : Where (int_>=0 (int_add (list_length l) (int_neg (i + 1))))} -> A |]
--   NatFold → [termQQ| Fun {Acc : Fun (Int+) -> Any} (Acc 0) (Fun (i : Int+) (Acc i) -> Acc (i + 1)) (n : Int+) -> Acc n |]
--   If → [termQQ| Fun {A} (cond : Bool) (Fun {_ : Eq cond true} -> A) (Fun {_ : Eq cond false} -> A) -> A |]
--   IntGte0 → [termQQ| Fun (Int) -> Bool |]
--   IntEq → [termQQ| Fun (Int) (Int) -> Bool |]
--   IntNeq → [termQQ| Fun (Int) (Int) -> Bool |]
--   TagEq → [termQQ| Fun (Tag) (Tag) -> Bool |]
--   W → [termQQ| Fun {u} (Type+ u) -> Type+ u |]
--   Wrap → [termQQ| Fun {A} (A) -> W A |]
--   Unwrap → [termQQ| Fun {A} (W A) -> A |]
--   Never → [termQQ| Type+ 0 |]
--   Any' → [termQQ| Type+ 0 |] where
--  where
--   opd d = Pi QNorm Nothing (Builtin $ Num d) $ Lambda $ Builtin $ Num d
--   op2d d = Pi QNorm Nothing (Builtin $ Num d) $ Lambda $ Pi QNorm Nothing (Builtin $ Num d) $ Lambda $ Builtin $ Num d

-- instMeta ∷ ∀ sig m. (Has Solve sig m) ⇒ Maybe Ident → ExVarId → Term → Term → m ()
-- instMeta = (\f a b c d → stackScope (\_ → "instMeta") $ f a b c d) \n1 (ExVarId var1) t1 →
--   let instMeta' ∷ Int → Term → m Term
--       instMeta' locs = \case
--         ExVar n2 (ExVarId var2) t2 →
--           if var2 <= var1
--             then pure $ ExVar n2 (ExVarId var2) t2
--             else do
--               u ← fresh
--               n ← freshIdent
--               let var1R = ExVar (Just n) (ExVarId $ var1 <> [u]) t2
--               writeMeta n2 (ExVarId var2) t2 locs var1R
--               pure $ var1R
--         uni@(UniVar _ uni2 _)
--           | [uni2] <= var1 → pure uni
--         App (Builtin W) a → pure $ Builtin W `App` a
--         App f a → runSeqResolve do
--           f' ← withResolved \_ → instMeta' locs f
--           a' ← withResolved \exs → instMeta' locs $ resolve exs a
--           pure $ App f' a'
--         FieldsLit fi flds → FieldsLit fi <$> traverse (bitraverse (instMeta' locs) (instMeta' locs)) flds
--         Concat a (FRecord b) →
--           runSeqResolve
--             $ Concat
--             <$> (withResolved \_ → instMeta' locs a)
--             <*> (FRecord <$> withResolved \exs → instMeta' locs $ resolve exs b)
--         Concat a (FRow (i, b)) → runSeqResolve do
--           a' ← withResolved \_ → instMeta' locs a
--           b' ← withResolved \exs → instMeta' (locs + 1) $ resolve' 1 exs $ unLambda b
--           pure $ Concat a' $ FRow (i, Lambda b')
--         Var x → pure $ Var x -- TODO: I hope this is correct, but needs to be rechecked.
--         Builtin x → pure $ Builtin x
--         BoolLit x → pure $ BoolLit x
--         NumLit x → pure $ NumLit x
--         TagLit x → pure $ TagLit x
--         Pi QNorm n inT outT → runSeqResolve do
--           inT' ← withResolved \_ → instMeta' locs inT
--           outT' ← withResolved \exs → instMeta' (locs + 1) $ resolve' 1 exs $ unLambda outT
--           pure $ Pi QNorm n inT' $ Lambda outT'
--         x → stackError \p → "instMeta (of" <+> pretty (tshow $ ExVarId var1) <> ")" <+> p x
--    in \val →
--         let r = writeMeta n1 (ExVarId var1) t1 0 =<< instMeta' 0 val
--          in case val of
--               ExVar _ var2 _ →
--                 if var2 == ExVarId var1
--                   then pure ()
--                   else r
--               _ → r

-- -- TODO: Use isEq.

-- -- | a <: b Check if type `a` is a subtype of type `b`.
subtype ∷ ∀ sig m. (Has Checker sig m) ⇒ Term → Term → m ()
subtype = \a b → error "hi"

--   stackScope (\p → p a <+> annotate (color Cyan) "<:" <+> p b) $ subtype' a b
--  where
--   -- Core subtyping logic based on the structure of the resolved types.
--   subtype' ∷ Term → Term → m ()
--   subtype' = curry \case
--     -- Existential Variables (?a <: ?b, ?a <: T, T <: ?a)
--     (ExVar _ ex1 _, ExVar _ ex2 _) | ex1 == ex2 → pure ()
--     (ExVar n1 ex1 ty1, t2) → instMeta n1 ex1 ty1 t2
--     (t1, ExVar n2 ex2 ty2) → instMeta n2 ex2 ty2 t1
--     -- Universal Variables (u1 <: u2) - Must be identical.
--     (UniVar _ id1 _, UniVar _ id2 _) | id1 == id2 → pure ()
--     -- T <: Pi QEra x:K. Body  => Introduce UniVar for x
--     (t, Pi QEra (Just n) k body) → do
--       uniId ← fresh
--       scopedUniVar (const pure) uniId
--         $ subtype t
--         $ applyLambda body
--         $ UniVar (Just n) uniId k
--     -- Pi QEra x:K. Body <: T => Introduce ExVar for x
--     (Pi QEra (Just n) k body, t) → do
--       exId ← fresh
--       scopedExVar (\_ _ → stackError \_ → "Unresolved existential" <+> pIdent n) (exId, k)
--         $ subtype (applyLambda body (ExVar (Just n) (ExVarId [exId]) k)) t

--     -- Function Types (Πx:T1.U1 <: Πy:T2.U2)
--     (Pi q1 n1 inT1 outT1, Pi q2 n2 inT2 outT2) | q1 == q2 → runSeqResolve do
--       -- Input types are contravariant (T2 <: T1)
--       withResolved \_ → subtype inT2 inT1
--       -- Output types are covariant
--       withResolved \exs → do
--         uniId ← fresh
--         scopedUniVar (const pure) uniId do
--           let var = UniVar (n1 <|> n2) uniId inT2
--           let outT1' = resolve exs $ applyLambda outT1 var
--           let outT2' = resolve exs $ applyLambda outT2 var
--           subtype outT1' outT2'
--     (Builtin (Num d1@(NumDesc nonneg1 bits1)), Builtin (Num d2@(NumDesc nonneg2 bits2))) →
--       let fits = case (nonneg1, nonneg2) of
--             (True, False) → bits1 < bits2 || bits2 == BitsInf
--             (False, True) → False
--             _ → bits1 <= bits2
--        in if fits then pure () else stackError \_ → "Cannot fit " <> pIdent (identOfBuiltin $ Num d1) <> " into " <> pIdent (identOfBuiltin $ Num d2)
--     (Builtin Never, _) → pure ()
--     (_, Builtin Any') → pure ()
--     -- Builtin Types (must be identical)
--     (Builtin a, Builtin b) | a == b → pure ()
--     (Var i, Var j) | i == j → pure ()
--     -- Type Universes (Type L1 <: Type L2 where L1 <= L2)
--     (App (Builtin TypePlus) a, App (Builtin TypePlus) b) → do
--       case (a, b) of
--         (NumLit x, NumLit y) | x <= y → pure ()
--         (NumLit 0, _) → pure ()
--         -- If one level is existential, unify it with the other level constraint.
--         (ExVar nA exA tyA, lvl2) → instMeta nA exA tyA lvl2
--         (lvl1, ExVar nB exB tyB) → instMeta nB exB tyB lvl1
--         _ → runSeqResolve do
--           r ← withResolved \_ → isEqUnify a b
--           case r of
--             EqYes → pure ()
--             _ → withResolved \exs → stackError \p → "Cannot subtype universes with levels:" <+> p (resolve exs a) <+> "<=" <+> p (resolve exs b)
--     (App (Builtin List) a, App (Builtin List) b) → subtype a b
--     (App (Builtin W) a, App (Builtin W) b) →
--       isEqUnify a b >>= \case
--         EqYes → pure ()
--         _ → stackError \p → "Cannot equate wrapped types" <+> p a <+> "and" <+> p b
--     (App (Builtin Row) a, App (Builtin Row) b) → subtype a b
--     (App (Builtin Row) a, App (Builtin TypePlus) u) → subtype a $ typOf u
--     (FieldsLit (FRow ()) (Vector' fields1), FieldsLit (FRow ()) fields2) →
--       let
--         fields1Drop fields1' name ty =
--           runSeqResolve
--             $ ifoldr
--               ( \i (name1, ty1) rec → do
--                   eqName ← withResolved \exs → isEqUnify (resolve exs name) (resolve exs name1)
--                   case eqName of
--                     EqYes → do
--                       withResolved \exs → subtype (resolve exs ty1) (resolve exs ty)
--                       withResolved \exs → pure $ bimap (resolve exs) (resolve exs) <$> deleteAt i fields1'
--                     EqUnknown → stackError \_ → "Unable to check field equality when subtyping"
--                     EqNot → rec
--               )
--               (stackError \_ → "Missing field from left side when subtyping")
--               fields1'
--        in
--         runSeqResolve
--           $ foldM_
--             (\fields1' (name, ty) → withResolved \exs → fields1Drop fields1' (resolve exs name) (resolve exs ty))
--             fields1
--             fields2
--     -- n : l1 \/ r1  <:  n : l2 \/ r2
--     (Concat l1 (FRow (n, lr1)), Concat l2 (FRow (_, lr2))) → runSeqResolve do
--       withResolved \_ → subtype l1 l2
--       uniId ← fresh
--       withResolved \exs → scopedUniVar (const pure) uniId do
--         let var = UniVar n uniId l1
--         let body1 = resolve exs $ applyLambda lr1 var
--         let body2 = resolve exs $ applyLambda lr2 var
--         subtype body1 body2

--     -- Catch-all: if no rule matches, check equality
--     (t1, t2) → runSeqResolve do
--       eq ← withResolved \_ → isEqUnify t1 t2
--       case eq of
--         EqYes → pure ()
--         _ → withResolved \exs → stackError \p → "Subtype check failed, no rule applies for:" <+> p (resolve exs t1) <+> "<:" <+> p (resolve exs t2)

runChecker' ∷ (Applicative m) ⇒ FreshC (ErrorC e (StateC (Vector Binding) (StateC Exs (ErrorC (Doc AnsiStyle) m)))) a → m (Either e a)
runChecker' =
  runContext
    . runError (pure . Left) (pure . Right)
    . evalFresh 0

checkSource ∷ ByteString → IO ()
checkSource source = do
  term ← either (fail . show) pure $ parse [] source
  (stacks, res) ← runStackAccC $ runChecker' $ infer term Infer
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
  res ← runStackPrintC $ runChecker' $ infer term Infer
  render case res of
    Left e → annotate (color Red) "error: " <> e
    Right r → pTerm [] r

checkFile ∷ FilePath → IO ()
checkFile file = checkSource =<< readFileBinary file

-- checkFileDebug ∷ FilePath → IO ()
-- checkFileDebug file = checkSourceDebug =<< readFileBinary file

main ∷ IO ()
main = pure ()
