{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use const" #-}
module Normalize where

import Arithmetic (normalizePoly)
import Control.Algebra
import Control.Carrier.Reader (runReader)
import Control.Carrier.State.Church (StateC (..), runState)
import Control.Effect.Reader (ask, local)
import Control.Effect.State (State, get, modify, state)
import Data.ByteString.Char8 (pack)
import Data.RRBVector (Vector, adjust', deleteAt, findIndexL, ifoldr, replicate, take, viewl, viewr, zip, (!?), (<|), (|>), imap, fromList)
import Language.Haskell.TH.Quote (QuasiQuoter (..))
import Parser (Bits (..), BlockF (..), BuiltinT (..), FieldsK (..), Ident (..), IsErased (..), Lambda (..), NumDesc (..), ParserContext (..), Quant (..), RefineK (..), Term (..), TermF (..), Vector' (..), builtinsList, dotvar, identOfBuiltin, nestedByP, nestedByP', parse, recordGet, splitAt3, traverseTermF, pattern TApp, pattern TBuiltin, regIdent, nestedBy')
import RIO hiding (Reader, Vector, ask, concat, drop, force, link, local, replicate, runReader, take, to, toList, try, zip, catch, reverse)
import System.IO.Unsafe (unsafePerformIO)
import Context (ScopesM, Imports (..), Binding, Scopes (..), EEntry (..), Epoch (..), Dyn (..), Rewrite (..), runScopes, runApp, fetchWith, getEpoch, getScopeId, stackLog, stackError)
import Control.Effect.Lift (Lift, sendM)
import Prettyprinter ((<+>))
import Control.Carrier.Lift (runM, LiftC (..))
import Data.Tuple (swap)
import qualified Data.IntMap.Strict as IM

-- Crazy thoughts:
-- 1) Normalizer has pretty simple logic, we could ± easily offload it to Rust.
-- It's just one big pattern matcher, how bad could it be? (famous last words)
-- 2) Deep pattern matching of rewrites & Arithmetic is a serious problem. However, we could "compact" patterns into one, or
-- track pattern-matching as we reconstruct the term from bottom up, never unwrapping results of nested normalization call.

-- TODO: Erasure is wrong... Verify for \f. f @4
-- TODO: Add `Thunk` Term, make `normalize` have a pure-heart with the capability to delay normalizing of subterms as `Thunk ctx`
-- Basically, we need to enrich term with information when it's needed, and `normalize` shouldn't normalize the term fully, instead just injecting Thunk's.

-- Builtins
-- (returns `n ** (Vec n Term -> Term)`)
appBuiltin ∷ Vector (Maybe Term) → BuiltinT → Vector Term → ScopesM (Maybe Term)
appBuiltin locals = curry \case
  ((Any'; Bool; Eq; Int' _; List; Never; OpaqueType{}; PropLteTrans; PropListViewlDec; Refl; RowPlus; Tag; TypePlus; W), _) → pure Nothing
  (Loop, [i0, f]) | not (isStuck i0) → fmap Just $ normalize' locals $ f `TApp` i0 `TApp` Term (Lam QNorm (Just $ regIdent "i") $ Lambda $ TBuiltin Loop `TApp` Term (Var 0) `TApp` f)
  (If, [Term (BoolLit cond), th, el]) → pure $ Just $ if cond then th else el
  (IntEq, [Term (NumLit a), Term (NumLit b)]) → pure $ Just $ Term $ BoolLit $ a == b
  (IntGte0, [Term (NumLit x)]) → pure $ Just $ Term $ BoolLit $ x >= 0
  ((IntAdd _; IntMul _; IntNeg _), _) → pure Nothing
  (ListIndexL, [Term (ListLit (Vector' vals)), Term (NumLit i)]) → pure $ vals !? fromIntegral i
  (ListLength, [Term (ListLit vals)]) → pure $ Just $ Term $ NumLit $ fromIntegral $ length vals
  (ListViewL, [Term (ListLit (Vector' vals))]) →
    pure $ viewl vals <&> \(left, rest) →
      Term $ FieldsLit (FRecord ()) [(Term $ TagLit (regIdent "left"), left), (Term $ TagLit (regIdent "rest"), Term $ ListLit $ Vector' rest)]
  (RecordDropFields, [Term (ListLit tags), a]) → Just <$> recordDropFields tags a
  (RecordGet, [name1, a]) →
    Just <$>
      let
        search a' = case unconsField a' of
          Nothing → pure $ recordGet name1 a'
          Just ((name2, v), rest) → isEq (name1, name2) >>= \case
            EqYes → pure v
            EqNot → search rest
            EqUnknown → pure $ recordGet name1 a'
        in search a
  (RecordKeepFields, [Term (ListLit tags), a]) → pure $ Just $ Term $ FieldsLit (FRecord ()) $ (\tag → (tag, recordGet tag a)) <$> tags
  (TagEq, [Term (TagLit a), Term (TagLit b)]) → pure $ Just $ Term $ BoolLit $ a == b
  (WUnwrap, [a]) → pure $ Just a
  (WWrap, [a]) → pure $ Just a
  ((Loop; If; IntEq; IntGte0; ListIndexL; ListLength; ListViewL; RecordDropFields; RecordGet; RecordKeepFields; TagEq; WWrap; WUnwrap), _) → pure Nothing
 where
  isStuck = unTerm >>> \case
    (NumLit{}; TagLit{}; BoolLit{}; ListLit{}; FieldsLit{}; Builtin{}; Lam{}; Pi{}; Concat{}) → False
    (BuiltinsVar{}; App{}; Var{}; Sorry; RefineGet{}; Block{}; AppErased{}; Refine{}; Import{}; ExVar{}; UniVar{}) → True
  -- Drop `x` from ListLit.
  listLitDrop ∷ Term → Vector' Term → ScopesM ListDropRes
  listLitDrop x (Vector' fi) =
    ifoldr
      ( \i n rec → isEq (x, n) >>= \case
          EqYes → pure $ TDFound $ Vector' $ deleteAt i fi
          EqNot → rec
          EqUnknown → pure $ TDUnknown
      )
      (pure TDMissing)
      fi
  recordDropFields ∷ Vector' Term → Term → ScopesM Term
  recordDropFields tags fields0 = case tags of
    Vector' (null → True) → pure $ Term $ FieldsLit (FRecord ()) []
    _ →
      let
        stuck = Term $ App (Term $ App (Term $ Builtin RecordDropFields) $ Term $ ListLit tags) fields0
       in
        case unconsField fields0 of
          Nothing → pure stuck
          Just ((n, v), fields) → listLitDrop n tags >>= \case
            TDFound tags' → recordDropFields tags' fields
            TDMissing →
              concat (Term $ FieldsLit (FRecord ()) [(n, v)]) <$> recordDropFields tags fields
            TDUnknown → pure stuck

-- | Intensional equality.
data EqRes
  = EqYes -- provably eq
  | EqNot -- provably uneq
  | EqUnknown
  deriving (Eq)

withBinding' ∷ Has (Lift ScopesM) sig m ⇒ Binding → m a → m a
withBinding' b act = do
  sendM @ScopesM $ modify @Scopes \(Scopes bs es rs) → Scopes (bs |> b) (es |> (Epoch 0, [])) rs
  res ← act
  sendM @ScopesM $ modify @Scopes \(Scopes bs es rs) →
    Scopes
      (maybe (error "Missing binding") fst $ viewr bs)
      (maybe (error "Missing ex scope") fst $ viewr es)
      rs
  pure res

withBinding :: Binding → ScopesM a → ScopesM a
withBinding b act = runM $ withBinding' b (LiftC act)

{- | Executes action in context with some marked EEntry region, returns the transformed EEntry region.
Basically, needed for EMarker + EVar pattern. Marker is needed to ensure the start is still identifiable.
TODO: NOT ERROR-SAFE!
-}
-- Generic since used by both normalizer & rewriter
withMarked ∷ Has (State Scopes) sig m ⇒ Vector EEntry → m a → m (Vector EEntry, a)
withMarked orig act = do
  scopeId ← getScopeId
  modify @Scopes \(Scopes bs es rs) → Scopes bs (adjust' scopeId (fmap (<> (EMarker <| orig))) es) rs
  res ← act
  transformed ← state @Scopes \(Scopes bs exs rs) →
    let
      (exsB, (scopeE, scope)) = fromMaybe (error "Missing ex scope") $ viewr exs
      (scope', transformed) =
        fix
          ( \rec →
              viewr >>> \case
                Just (rest, EMarker) → (rest, [])
                Just (rest, entry) → (|> entry) <$> rec rest
                Nothing → error "Marker disappeared"
          )
          scope
     in
      (Scopes bs (exsB |> (scopeE, scope')) rs, transformed)
  pure (transformed, res)

fDyn ∷ Epoch → Term → TermF Dyn
fDyn e = run . traverseTermF (pure . Dyn e) (\_n → pure . Lambda . Dyn e . unLambda) . unTerm

--
fetchT ∷ Dyn → ScopesM Term
fetchT = fetchWith normalize

fetchLambda ∷ Lambda Dyn → ScopesM (Lambda Term)
fetchLambda = fmap Lambda . fetchWith (normalize' [Nothing]) . unLambda

-- | Only normalized & non-ExVar
-- Please look rollbackNonEq
traverseIsEq :: Has (Lift ScopesM) sig m ⇒ ((Term, Term) → m EqRes) → (Int → (Lambda Term, Lambda Term) → m EqRes) → (TermF Term, TermF Term) → m EqRes
traverseIsEq c cNest (l0, r0) = sendM @ScopesM getEpoch >>= \e0 → case (fDyn e0 $ Term l0, fDyn e0 $ Term r0) of
  ((Lam QEra _ _; BuiltinsVar; Block{}; AppErased{}; Refine (RefinePost{}; RefinePre{}); RefineGet _ (_, Nothing); Import{}), _) → undefined
  (_, (Lam QEra _ _; BuiltinsVar; Block{}; AppErased{}; Refine (RefinePost{}; RefinePre{}); RefineGet _ (_, Nothing); Import{})) → undefined
  (ExVar{}, _) → pure EqUnknown -- We don't handle those here, explicitly. Up to users.
  (_, ExVar{}) → pure EqUnknown
  -- Unknown
  (Var a, Var b)
    | a == b → pure EqYes
  (Var _, _) → pure EqUnknown
  (_, Var _) → pure EqUnknown
  (UniVar i1 _, UniVar i2 _)
    | i1 == i2 → pure EqYes
  (UniVar{}, _) → pure EqUnknown
  (_, UniVar{}) → pure EqUnknown
  (App f1 a1, App f2 a2) →
    try (cM (fetchT f1) (fetchT f2))
      $ try (cM (fetchT a1) (fetchT a2))
      $ pure EqYes
  (App{}, _) → pure EqUnknown
  (_, App{}) → pure EqUnknown
  (Sorry, _) → pure EqUnknown
  (_, Sorry) → pure EqUnknown
  (RefineGet e1 (skips1, Just f1), RefineGet e2 (skips2, Just f2)) →
    pure $ if e1 == e2 && skips1 == skips2 && f1 == f2 then EqYes else EqUnknown
  (RefineGet{}, _) → pure EqUnknown
  (_, RefineGet{}) → pure EqUnknown
  (Concat a1 (FRecord b1), Concat a2 (FRecord b2)) →
    try (cM (fetchT a1) (fetchT a2))
      $ try (cM (fetchT b1) (fetchT b2))
      $ pure EqYes
  (Concat _ (FRecord _), _) → pure EqUnknown
  (_, Concat _ (FRecord _)) → pure EqUnknown
  -- Literals
  (NumLit a, NumLit b)
    | a == b → pure EqYes
  (NumLit _, _) → pure EqNot
  (TagLit a, TagLit b)
    | a == b → pure EqYes
  (TagLit _, _) → pure EqNot
  (BoolLit a, BoolLit b)
    | a == b → pure EqYes
  (BoolLit _, _) → pure EqNot
  (ListLit (Vector' as), ListLit (Vector' bs)) →
    if length as /= length bs
      then pure EqNot
      else foldr (\(a, b) next → force (cM (fetchT a) (fetchT b)) next) (pure EqYes) (zip as bs)
  (ListLit _, _) → pure EqNot
  (FieldsLit f1 (Vector' as0), FieldsLit f2 (Vector' bs0))
    | f1 == f2 →
        if length as0 /= length bs0
          then pure EqNot
          else
            foldr
              ( \(tag1, val1) recO bs →
                  ifoldr
                    ( \i (tag2, val2) recI →
                        cM (fetchT tag1) (fetchT tag2) >>= \case
                          EqYes → force (cM (fetchT val1) (fetchT val2)) $ recO $ deleteAt i bs
                          EqNot → recI
                          EqUnknown → pure EqUnknown
                    )
                    (pure EqNot)
                    bs
              )
              (\_ → pure EqYes)
              as0
              bs0
  (FieldsLit{}, _) → pure EqNot
  (Builtin a, Builtin b)
    | a == b → pure EqYes
  (Builtin _, _) → pure EqNot
  (Lam QNorm i1 bod1, Lam QNorm i2 bod2) →
    withBinding' (QNorm, i1 <|> i2, Nothing, Term $ Builtin Any')
      $ cNestM 1 (fetchLambda bod1) (fetchLambda bod2)
  (Lam QNorm _ _, _) → pure EqNot
  (Pi q1 i1 inT1 outT1, Pi q2 i2 inT2 outT2)
    | q1 == q2 →
        force (cM (fetchT inT1) (fetchT inT2)) do
          inT1' ← sendM @ScopesM $ fetchT inT1
          withBinding' (QNorm, i1 <|> i2, Nothing, inT1') $ cNestM 1 (fetchLambda outT1) (fetchLambda outT2)
  (Pi{}, _) → pure EqNot
  (Refine (RefinePreTy i1 ann1 base1), Refine (RefinePreTy _i2 ann2 base2)) → goDepPair (Just i1) (ann1, base1) (ann2, base2)
  (Refine (RefinePostTy base1 i1 ann1), Refine (RefinePostTy base2 _i2 ann2)) → goDepPair (Just i1) (base1, ann1) (base2, ann2)
  (Refine{}, _) → pure EqNot
  (Concat l1 (FRow r1), Concat l2 (FRow r2)) → goDepPair (Just dotvar) (l1, r1) (l2, r2)
  (Concat _ (FRow _), _) → pure EqNot
  where
  -- `c` with monadic args
  cM aM bM = c =<< ((,) <$> sendM @ScopesM aM <*> sendM @ScopesM bM)
  cNestM i aM bM = cNest i =<< ((,) <$> sendM @ScopesM aM <*> sendM @ScopesM bM)
  try act cont =
    act >>= \case
      EqYes → cont
      _ → pure EqUnknown
  force act cont =
    act >>= \case
      EqYes → cont
      x → pure x
  goDepPair i (l1, r1) (l2, r2) =
    force (cM (fetchT l1) (fetchT l2))
      $ withBinding' (QNorm, i, Nothing, Term $ Builtin Any')
      $ cNestM 1 (fetchLambda r1) (fetchLambda r2)

rollbackNonEq :: ScopesM EqRes → ScopesM EqRes
rollbackNonEq act = StateC \cont s0 →
  runState (\s1 res →
      if res == EqYes
        then cont s1 res
        else cont s0 res
  ) s0 act

isEq ∷ (Term, Term) → ScopesM EqRes
isEq = rollbackNonEq . runM . fix \rec → bimap unTerm unTerm >>> \case
  (ExVar{}, _) → pure EqUnknown
  (_, ExVar{}) → pure EqUnknown
  x → traverseIsEq rec (\_ (l, r) → rec (unLambda l, unLambda r)) x

-- | Produces a non-dependent concat (of normalized terms)
concat ∷ Term → Term → Term
concat = curry \case
  (unTerm → FieldsLit (FRecord ()) l, unTerm → FieldsLit (FRecord ()) r) → Term $ FieldsLit (FRecord ()) $ l <> r
  (l, r) → Term $ Concat l $ FRecord r

unconsField ∷ Term → Maybe ((Term, Term), Term)
unconsField =
  unTerm >>> \case
    Concat (unTerm → Concat l (FRecord m)) (FRecord r) → unconsField $ concat l $ concat m r
    Concat (unTerm → FieldsLit (FRecord ()) (Vector' fi)) (FRecord r) → case viewl fi of
      Just (x, xs) → Just (x, concat (Term $ FieldsLit (FRecord ()) $ Vector' xs) r)
      Nothing → unconsField r
    FieldsLit (FRecord ()) (Vector' fi) → case viewl fi of
      Just (x, xs) → Just (x, Term $ FieldsLit (FRecord ()) $ Vector' xs)
      Nothing → Nothing
    _ → Nothing

numDecDispatch ∷ NumDesc → (∀ x. (Integral x, Bounded x) ⇒ Proxy x → a) → a → a
numDecDispatch desc f inf = case desc of
  NumFin signed bits → case (signed, bits) of
    (False, Bits8) → f (Proxy @Int8)
    (True, Bits8) → f (Proxy @Word8)
    (False, Bits16) → f (Proxy @Int16)
    (True, Bits16) → f (Proxy @Word16)
    (False, Bits32) → f (Proxy @Int32)
    (True, Bits32) → f (Proxy @Word32)
    (False, Bits64) → f (Proxy @Int64)
    (True, Bits64) → f (Proxy @Word64)
  NumInf → inf

data ListDropRes = TDFound !(Vector' Term) | TDMissing | TDUnknown

tryRewrite ∷ (Int, Rewrite) → Term → ScopesM (Maybe Term)
tryRewrite (nest, Rewrite forallsCount lfromto0) t = do
  -- We'll use IORefs here to store variables. Just not to ruin monadic stack.
  -- Honestly, I don't see an issue with this, although this is *technically* a cutch.
  -- TODO: Arrays?
  -- stores instantiated meta-variables, with indices adjusted for the current scope.
  -- params :: Vector (IORef (Maybe Term)) ← for ([1..forallsCount] :: Vector Int) \_ → sendIO $ newIORef Nothing
  let
    inst :: Int → Term → StateC (IntMap Term) (LiftC ScopesM) EqRes
    inst relI curr = do
      writtenM ← state @(IntMap Term) $ swap . IM.insertLookupWithKey (\_k _new written → written) relI curr
      case writtenM of
        Nothing → pure EqYes
        Just written → lift (lift $ isEq (curr, written))
    match :: Int → (Term, Term) → StateC (IntMap Term) (LiftC ScopesM) EqRes
    match locs = \case
      (a0@(Term (Var i)), b)
        | i < locs → -- Locally bound, shared for both
          pure $ if a0 == b then EqYes else EqUnknown
        | i < locs + forallsCount → do -- Rewrite parameter
          let relI = i - locs -- index of rewrite parameter
          case nestedBy' 0 b (-locs) of
            Just curr → inst relI curr
            Nothing → pure EqUnknown
        | otherwise → pure $ if Term (Var $ i - forallsCount + nest) == b then EqYes else EqUnknown
      (a0@(Term (RefineGet i (skips, final))), b)
        | i < locs → pure $ if a0 == b then EqYes else EqUnknown
        | i < locs + forallsCount → do -- TODO: write tests
          let relI = i - locs
          case b of
            Term (RefineGet i2 (skips2, final2)) | i2 >= locs && skips == skips2 && final == final2 →
              inst relI $ Term $ Var (i2 - locs)
            _ → pure EqUnknown
        | otherwise → pure $ if Term (RefineGet (i - forallsCount + nest) (skips, final)) == b then EqYes else EqUnknown
      x → traverseIsEq (match locs) (\i → match (locs+i) . bimap unLambda unLambda) (bimap unTerm unTerm x)
  (params, matchesPattern) ← runM $ runState @(IntMap Term) (curry pure) mempty $ match 0 (fst $ unLambda lfromto0, t)
  if matchesPattern == EqYes
    then do
      -- All these exist in the same, current scope.
      let valsCurrScope = fromList (snd <$> IM.toDescList params)
      unless (length valsCurrScope == forallsCount) $ stackError \_ → "Not all existentials resolved"
      let vals = imap (\i → Just . (`nestedByP` i)) valsCurrScope
      final ← normalize' vals (nestedByP' forallsCount (snd $ unLambda lfromto0) nest)
      stackLog \p → "Rewrote" <+> p t <+> "with" <+> p final
      pure $ Just final
    else pure Nothing

traverseNormTermF ∷ (Vector (Maybe Term) → Term → ScopesM Term) → Vector (Maybe Term) → TermF Term → ScopesM Term
traverseNormTermF c locals t0 = rewr =<< trav
 where
  rewr res = do
    -- traceM "Rewriting"
    scope ← getScopeId
    Scopes _ _ rs00 ← get
    ifoldr
      ( \rewrI (oldScope, oldRewr) rec → do
          Scopes _ _ rs0 ← get
          modify \(Scopes bs exs rs) → Scopes bs exs $ take rewrI rs
          let nest = (scope - oldScope) + (length locals - countErasedLocals)
          replacement ← tryRewrite (nest, oldRewr) res
          modify \(Scopes bs exs _rs) → Scopes bs exs rs0
          maybe rec pure replacement
      )
      (pure res)
      rs00
  travVar globalI =
    -- TODO: deduplicate.
    if globalI < length locals
      then
        pure
          $ let
              (_, b, potentiallyErasable) = splitAt3 (length locals - 1 - globalI) locals
              updatedGlobalI = globalI - countErased potentiallyErasable
             in
              case b of
                Just (Just v) → nestedByP v updatedGlobalI
                _ → Term $ Var updatedGlobalI
      else do
        Scopes globals _ _ ← get @Scopes
        let updatedGlobalI = globalI - countErasedLocals
        pure case globals !? (length globals - 1 - (globalI - length locals)) of
          Just (_, _, Just raw, _) → nestedByP raw $ updatedGlobalI + 1
          _ → Term $ Var updatedGlobalI
  trav = case t0 of
    BuiltinsVar → pure builtinsVar
    Lam QEra _ body → c (locals |> Just undefined) $ unLambda body -- TODO: Total?
    App f a → do
      f' ← c locals f
      a' ← c locals a
      let locals' = replicate (length locals - countErasedLocals) Nothing
      case f' of
        Term (Lam QNorm _ body) → c (locals' |> Just a') $ unLambda body
        _ →
          let
            collect disf disargs = case disf of
              TApp disff disfa → collect disff (disfa <| disargs)
              _ → (disf, disargs)
            (f'', a'') = collect f' [a']
           in
            case f'' of
              TBuiltin bf →
                appBuiltin locals' bf a'' <&> \case
                  Just r → r
                  Nothing → normalizePoly $ f' `TApp` a'
              _ → pure $ f' `TApp` a'
    -- pure $ postApp f' a'
    Var globalI → travVar globalI
    AppErased f _a → c locals f
    Refine (RefinePre _ann base) → c locals base
    Refine (RefinePost base _ann) → c locals base
    RefineGet oldX (_, Nothing) → travVar oldX
    RefineGet oldX (skips1, final1) → do
      termX ← travVar oldX
      pure $ Term $ case unTerm termX of
        Var x → RefineGet x (skips1, final1)
        _ → if oldX < length locals
          then error "Internal error: cannot substitute into a RefineGet"
          else RefineGet (oldX - countErasedLocals) (skips1, final1) -- safe, because global bindings aren't erased.
    Block (BlockLet _q _name _ty val into) → do
      val' ← c locals val
      c (locals |> Just val') $ unLambda into
    Block (BlockRewrite _prf into) → c locals into
    Block (BlockOpaque oid _args _body into) → c (locals |> Just (TBuiltin $ OpaqueType oid)) (unLambda into)
    Concat a b → case b of
      FRecord b' → concat <$> c locals a <*> c locals b'
      FRow b' → Term <$> (Concat <$> c locals a <*> (FRow . Lambda <$> c (locals |> Nothing) (unLambda b')))
    ExVar (i, subi) → do
      Scopes globals exs _ ← get @Scopes
      let valtyM = do
            (_, scope) ← exs !? i
            ind ←
              findIndexL
                ( \case
                    EVar subi2 _ → subi == subi2
                    _ → False
                )
                scope
            EVar _ valty0 ← scope !? ind
            pure valty0
      case valtyM of
        Just (Left val) → pure $ uncurry nestedByP' val $ length locals + (length globals - i) -- no -1 because of ridiculous scope counting
        _ → pure $ Term $ ExVar (i, subi)
    Import (fromMaybe (error "Unresolved import") → n) _ → do
      Imports imps ← ask
      pure $ maybe (error "Incomplete context") fst $ imps !? n
    _ → Term <$> traverseTermF (c locals) (\n → fmap Lambda . c (locals <> replicate n Nothing) . unLambda) t0
  countErasedLocals = countErased locals
  countErased = foldl' (\acc e → if isJust e then acc + 1 else acc) 0

builtinsVar ∷ Term
builtinsVar = Term $ FieldsLit (FRecord ()) $ Vector' $ (\b → (Term $ TagLit $ identOfBuiltin b, Term $ Builtin b)) <$> builtinsList

rewrite ∷ (Int → Term → ScopesM (Maybe Term)) → Vector (Maybe Term) → Term → ScopesM Term
rewrite rewriter = fix \rec locals t →
  rewriter (length locals) t >>= \case
    Just u → pure u
    Nothing → traverseNormTermF rec locals $ unTerm t

normalize' ∷ Vector (Maybe Term) → Term → ScopesM Term
normalize' = rewrite (\_ _ → pure Nothing)

normalize ∷ Term → ScopesM Term
normalize = normalize' []

applyLambda ∷ Lambda Term → Term → ScopesM Term
applyLambda bod val = normalize' [Just val] $ unLambda bod

-- | Apply `x.@_@_@_...` to a lambda.
applyLambdaRefineGetSkip ∷ Int → Int → Lambda Term → Term
applyLambdaRefineGetSkip binding newSkips =
  unLambda
    >>> let
          shift currI = do
            -- True on match
            locs ← ask
            pure $ case compare currI locs of
              LT → (currI, False)
              EQ → (binding + locs, True)
              GT → (currI - 1, False)
         in
          run . runReader @Int 0 . fix \rec →
            unTerm >>> fmap Term . \case
              Var currI → Var . fst <$> shift currI
              RefineGet currI (skips, Just f) → do
                (newI, match) ← shift currI
                pure $ RefineGet newI (if match then skips + newSkips else skips, Just f)
              x → traverseTermF rec (\n → fmap Lambda . local @Int (+ n) . rec . unLambda) x

{- | Parse builtin
Just a variation of parseQQ that has all the builtins in scope from the start.
-}
termQQ ∷ QuasiQuoter
termQQ =
  let
    wher = Term $ Lam QNorm (Just $ regIdent "n") $ Lambda $ Term $ Term (Term (Builtin Eq) `App` Term (Var 0)) `App` Term (BoolLit True)
    sub = Term $ Lam QNorm (Just (regIdent "a")) (Lambda (Term (Lam QNorm (Just (regIdent "b")) (Lambda (Term (App (Term (App (Term (Builtin (IntAdd NumInf))) (Term (App (Term (App (Term (Builtin (IntMul NumInf))) (Term (NumLit (-1))))) (Term (Var 0)))))) (Term (Var 1))))))))
    lte = Term{unTerm = Lam QNorm (Just (regIdent "a")) (Lambda{unLambda = Term{unTerm = Lam QNorm (Just (regIdent "b")) (Lambda{unLambda = Term{unTerm = App (Term{unTerm = Builtin IntGte0}) (Term{unTerm = App (Term{unTerm = App (Term{unTerm = Builtin (IntAdd NumInf)}) (Term{unTerm = App (Term{unTerm = App (Term{unTerm = Builtin (IntMul NumInf)}) (Term{unTerm = NumLit (-1)})}) (Term{unTerm = Var 1})})}) (Term{unTerm = Var 0})})}})}})}
    lt = Term{unTerm = Lam QNorm (Just (regIdent "a")) (Lambda{unLambda = Term{unTerm = Lam QNorm (Just (regIdent "b")) (Lambda{unLambda = Term{unTerm = App (Term{unTerm = Builtin IntGte0}) (Term{unTerm = App (Term{unTerm = App (Term{unTerm = Builtin (IntAdd NumInf)}) (Term{unTerm = App (Term{unTerm = App (Term{unTerm = Builtin (IntAdd NumInf)}) (Term{unTerm = App (Term{unTerm = App (Term{unTerm = Builtin (IntMul NumInf)}) (Term{unTerm = NumLit (-1)})}) (Term{unTerm = Var 1})})}) (Term{unTerm = Var 0})})}) (Term{unTerm = NumLit (-1)})})}})}})}
    intp = Term{unTerm = Refine (RefinePostTy (Term{unTerm = Builtin (Int' NumInf)}) (regIdent "pos") (Lambda{unLambda = Term{unTerm = App (Term{unTerm = App (Term{unTerm = Builtin Eq}) (Term{unTerm = App (Term{unTerm = Builtin IntGte0}) (Term{unTerm = Var 0})})}) (Term{unTerm = BoolLit True})}}))}
    scope ∷ Vector (Maybe Ident, Term)
    scope =
      ((\b → (Just $ identOfBuiltin b, Term $ Builtin b)) <$> builtinsList)
        <> [ (Just $ Ident "+" True, Term $ Builtin $ IntAdd NumInf)
           , (Just $ Ident "-" True, sub)
           , (Just $ regIdent "Where", wher)
           , (Just $ Ident "<=" True, lte)
           , (Just $ Ident "<" True, lt)
           , (Just $ regIdent "Int+", intp)
           ]
   in
    QuasiQuoter
      { quoteExp = \s → do
          (term, _) ← case parse (ParserContext (IsErased False) $ (QNorm,) . fst <$> scope) 0 (pack s) of
            Left e → fail $ "termQQ: Parse error: " ++ show e
            Right t → pure t
          let normed = either (error . show) id $ snd $ unsafePerformIO $ runApp $ runScopes (Imports []) $ normalize' (Just . snd <$> scope) term
          ⟦normed⟧
      , quotePat = error "termQQ: No pattern support"
      , quoteType = error "termQQ: No type support"
      , quoteDec = error "termQQ: No declaration support"
      }
