module Normalize where

import Control.Algebra
import Control.Carrier.Empty.Church (runEmpty)
import Control.Carrier.State.Church (StateC, evalState)
import Control.Effect.Empty (empty)
import Control.Effect.State (State, get, modify)
import Data.ByteString.Char8 (pack)
import Data.RRBVector (Vector, deleteAt, ifoldr, splitAt, viewl, viewr, (!?), (|>))
import Language.Haskell.TH.Quote (QuasiQuoter (..))
import Parser (Bits (..), BlockF (..), BuiltinT (..), ContextEntry (..), Fields (..), Ident (..), Lambda (..), N (..), NumDesc (..), Quant (..), Term (..), TermF (..), Vector' (..), builtinsList, ctxFindBinding, ctxFindEx, identOfBuiltin, nestedByP, parse, recordGet, traverseTermF, unwrap)
import RIO hiding (Reader, Vector, ask, concat, drop, force, link, local, replicate, runReader, to, toList, try)

-- TODO: Erasure is wrong... Verify for \f. f @4

type Context = State (Vector ContextEntry)

unwrapM ∷ (Has Context sig m) ⇒ Term → m (TermF Term)
unwrapM t = (\ctx → unwrap ctx t) <$> get

withEntry ∷ (Has Context sig m) ⇒ ContextEntry → m a → m a
withEntry e act = do
  modify (|> e)
  r ← act
  modify (maybe (error "impossible") fst . viewr @ContextEntry)
  pure r

runContext ∷ StateC (Vector ContextEntry) Identity a → a
runContext = runIdentity . evalState []

-- data Context m a where
--   WithBinding :: Binding → m a → Context m a
--   GetBinding :: Int → Context m (Maybe Binding)
--   GetMeta :: Int → Context m (Maybe Term)

-- -- | Context that just contains bindings
-- data ContextBindsC m a = ContextBindsC { unContextBindsC :: ReaderC ParserContext m a }

-- instance Algebra sig m ⇒ Algebra (Context :+: sig) (ContextBindsC m) where
--   alg hdl sig ctx = ContextBindsC case sig of
--     L (WithBinding b act) → local (|> b)
--     R other → alg (unContextBindsC . hdl) (R other) ctx

-- | Intensional equality.
data EqRes
  = EqYes -- provably eq
  | EqNot -- provably uneq
  | EqUnknown

isEq' ∷ (Has Context sig m) ⇒ ((Int, Vector' Int) → TermF Term → m ()) → Term → Term → m EqRes
isEq' f l0 r0 =
  ((,) <$> unwrapM l0 <*> unwrapM r0) >>= \case
    (Block{}, _) → undefined
    (_, Block{}) → undefined
    (AppErased{}, _) → undefined
    (_, AppErased{}) → undefined
    (Lam QEra _ _, _) → undefined
    (_, Lam QEra _ _) → undefined
    (ExVar i, t) → f i t $> EqYes
    (t, ExVar i) → f i t $> EqYes
    (Var a, Var b)
      | a == b → pure EqYes
    (Var _, _) → pure EqUnknown
    (_, Var _) → pure EqUnknown
    (UniVar i1, UniVar i2)
      | i1 == i2 → pure EqYes
    (UniVar{}, _) → pure EqUnknown
    (_, UniVar{}) → pure EqUnknown
    (App f1 a1, App f2 a2) →
      try (isEq' f f1 f2)
        $ try (isEq' f a1 a2)
        $ pure EqYes
    (App{}, _) → pure EqUnknown
    (_, App{}) → pure EqUnknown
    (Sorry, _) → pure EqUnknown
    (_, Sorry) → pure EqUnknown
    -- Literals
    (Lam QNorm i bod1, Lam QNorm _ bod2) → withEntry (ContextBinding (QNorm, i, Nothing, Term $ Builtin Any')) $ isEq' f (unLambda bod1) (unLambda bod2)
    (Lam QNorm _ _, _) → pure EqNot
    (NumLit a, NumLit b)
      | a == b → pure EqYes
    (NumLit _, _) → pure EqNot
    (TagLit a, TagLit b)
      | a == b → pure EqYes
    (TagLit _, _) → pure EqNot
    (BoolLit a, BoolLit b)
      | a == b → pure EqYes
    (BoolLit _, _) → pure EqNot
    (Builtin a, Builtin b)
      | a == b → pure EqYes
    (Builtin _, _) → pure EqNot
    (_, Builtin _) → pure EqNot
    (BuiltinsVar, BuiltinsVar) → pure EqYes
    (BuiltinsVar, _) → pure EqNot
    (_, BuiltinsVar) → pure EqNot
    (Pi q1 i1 inT1 outT1, Pi q2 i2 inT2 outT2)
      | q1 == q2 →
          force (isEq' f inT1 inT2)
            $ withEntry (ContextBinding (QNorm, i1 <|> i2, Nothing, inT1))
            $ isEq' f (unLambda outT1) (unLambda outT2)
    (Pi{}, _) → pure EqNot
    (Concat _ _, _) → error "TODO isEq Concat"
    (ListLit (Vector' (viewl → Just (x, xs))), ListLit (Vector' (viewl → Just (y, ys)))) →
      force (isEq' f x y) $ isEq' f (Term $ ListLit $ Vector' xs) (Term $ ListLit $ Vector' $ ys)
    (ListLit (Vector' (null → True)), ListLit (Vector' (null → True))) → pure EqYes
    (ListLit _, _) → pure EqNot
    -- TODO: This is greedy, which is bad. Should uwrap lazily.
    (FieldsLit f1 (Vector' (viewl → Just ((tagx, x), xs))), FieldsLit f2 (Vector' origY))
      | f1 == f2 →
          ifoldr
            ( \i (tagy, y) rec →
                isEq' f tagx tagy
                  >>= \case
                    EqYes →
                      force (isEq' f x y)
                        $ isEq'
                          f
                          (Term $ FieldsLit f1 $ Vector' xs)
                          (Term $ FieldsLit f1 $ Vector' $ deleteAt i origY)
                    EqNot → rec
                    EqUnknown → pure EqUnknown
            )
            (pure EqNot)
            origY
    (FieldsLit f1 (Vector' (null → True)), FieldsLit f2 (Vector' (null → True))) | f1 == f2 → pure EqYes
    (FieldsLit{}, _) → pure EqNot
 where
  -- TODO: FRow???
  try act cont =
    act >>= \case
      EqYes → cont
      _ → pure EqUnknown
  force act cont =
    act >>= \case
      EqYes → cont
      x → pure x

isEq ∷ N Term → N Term → EqRes
isEq a b = runContext $ runEmpty (pure EqUnknown) pure $ isEq' (\_ _ → empty) (unN a) (unN b)

-- | Produces a non-dependent concat.
concat ∷ N Term → N Term → N (TermF Term)
concat l0 r0 = N $ case (unN l0, unN r0) of
  (Term (FieldsLit (FRecord ()) l), Term (FieldsLit (FRecord ()) r)) → FieldsLit (FRecord ()) $ l <> r
  (l, r) → Concat l $ FRecord r

unconsField ∷ N Term → Maybe ((N Term, N Term), N Term)
unconsField =
  unTerm . unN >>> \case
    Concat (Term (Concat l (FRecord m))) (FRecord r) → unconsField $ N $ Term $ unN $ concat (N l) $ N $ Term $ unN $ concat (N m) (N r)
    Concat (Term (FieldsLit (FRecord ()) (Vector' fi))) (FRecord r) → case viewl fi of
      Just (x, xs) → Just (bimap N N $ x, N $ Term $ unN $ concat (N $ Term $ FieldsLit (FRecord ()) $ Vector' xs) $ N r)
      Nothing → unconsField $ N r
    FieldsLit (FRecord ()) (Vector' fi) → case viewl fi of
      Just (x, xs) → Just (bimap N N x, N $ Term $ FieldsLit (FRecord ()) $ Vector' xs)
      Nothing → Nothing
    _ → Nothing

repeat ∷ Integer → (a → a) → a → a
repeat n f = case n of
  0 → id
  _ → f . repeat (n - 1) f

-- TODO: Really simple, expand upon.
unplus ∷ N Term → (Maybe (N Term), Integer)
unplus (N (Term (NumLit n))) | n >= 0 = (Nothing, n)
unplus (N (Term (Term (Term (Builtin (Add (NumDesc True BitsInf))) `App` a) `App` Term (NumLit n)))) = (+ n) <$> unplus (N a)
unplus x = (Just x, 0)

numDecDispatch ∷ NumDesc → (∀ x. (Integral x, Bounded x) ⇒ Proxy x → a) → (Bool → a) → a
numDecDispatch (NumDesc signed bits) f inf = case (signed, bits) of
  (False, Bits8) → f (Proxy @Int8)
  (True, Bits8) → f (Proxy @Word8)
  (False, Bits16) → f (Proxy @Int16)
  (True, Bits16) → f (Proxy @Word16)
  (False, Bits32) → f (Proxy @Int32)
  (True, Bits32) → f (Proxy @Word32)
  (False, Bits64) → f (Proxy @Int64)
  (True, Bits64) → f (Proxy @Word64)
  (_, BitsInf) → inf signed

data ListDropRes = TDFound !(Vector' Term) | TDMissing | TDUnknown

-- | Processes application of `f` onto `a`.
postApp ∷ N Term → N Term → N (TermF Term)
postApp f00 a00 = N $ case (unTerm $ unN f00, unN a00) of
  (Lam QNorm _ bod, a) → unTerm $ unN $ applyLambda (N bod) (N a)
  (App (Term (Builtin RecordGet)) name1, a) →
    let
      search a' = case unconsField a' of
        Nothing → recordGet name1 $ unN a'
        Just ((name2, v), rest) → case isEq (N name1) name2 of
          EqYes → unN v
          EqNot → search rest
          EqUnknown → recordGet name1 $ unN a'
     in
      unTerm $ search $ N a
  (Term (Builtin RecordKeepFields) `App` Term (ListLit tags), a) → FieldsLit (FRecord ()) $ (\tag → (tag, recordGet tag a)) <$> tags
  (Term (Builtin RecordDropFields) `App` Term (ListLit tags), a) → unTerm $ recordDropFields tags a
  (Builtin ListLength, Term (ListLit (Vector' fi))) → NumLit $ fromIntegral $ length fi
  (f@(Term (Term (Builtin ListIndexL) `App` Term (ListLit (Vector' vals))) `App` Term (NumLit i)), a) → case vals !? fromIntegral i of
    Just v → unTerm v
    Nothing → App (Term f) a
  (Term (Term (Builtin NatFold) `App` start) `App` step, n) →
    let
      (nTM, nV) = unplus (N n)
     in
      -- TODO: causes constant re-normalization of `int+_fold` args.
      unTerm
        $ (if nV > 0 then unN . runContext . normalize else id)
        $ repeat nV (Term . App step)
        $ case nTM of
          Nothing → start
          Just (N nT) → Term $ Term (Term (Term (Builtin NatFold) `App` start) `App` step) `App` nT
  (Term (Term (Builtin If) `App` (Term (BoolLit cond))) `App` thenBranch, elseBranch) →
    if cond then unTerm thenBranch else unTerm elseBranch
  (Builtin IntGte0, Term (NumLit x)) → BoolLit $ x >= 0
  (Term (Builtin IntEq) `App` Term (NumLit l), Term (NumLit r)) → BoolLit $ l == r
  (Term (Builtin IntNeq) `App` Term (NumLit l), Term (NumLit r)) → BoolLit $ l /= r
  (Term (Builtin Wrap) `App` _ty, b) → unTerm b
  (Term (Builtin Unwrap) `App` _ty, b) → unTerm b
  -- Add
  (Term (Builtin (Add d)) `App` a, Term (NumLit b))
    | b == 0 → unTerm a
    | Term (NumLit a') ← a → NumLit $ numDecDispatch d (\(_ ∷ Proxy x) → fromIntegral @x $ fromIntegral a' + fromIntegral b) (\_ → a' + b)
  -- Sub
  (Builtin (IntNeg d), Term (NumLit x)) → NumLit $ numDecDispatch d (\(_ ∷ Proxy x) → fromIntegral @x $ -fromIntegral x) (\_ → -x)
  (f, a) → App (Term f) a
 where
  -- Drop `x` from ListLit.
  listLitDrop ∷ Term → Vector' Term → ListDropRes
  listLitDrop x (Vector' fi) =
    ifoldr
      ( \i n rec → case isEq (N x) (N n) of
          EqYes → TDFound $ Vector' $ deleteAt i fi
          EqNot → rec
          EqUnknown → TDUnknown
      )
      TDMissing
      fi

  recordDropFields ∷ Vector' Term → Term → Term
  recordDropFields tags fields0 = case tags of
    Vector' (null → True) → Term $ FieldsLit (FRecord ()) []
    _ →
      let
        stuck = Term $ App (Term $ App (Term $ Builtin RecordDropFields) $ Term $ ListLit tags) fields0
       in
        case unconsField (N fields0) of
          Nothing → stuck
          Just ((N n, N v), fields) → case listLitDrop n tags of
            TDFound tags' → recordDropFields tags' $ unN fields
            TDMissing →
              Term $ unN $ concat (N $ Term $ FieldsLit (FRecord ()) [(n, v)]) $ N $ recordDropFields tags (unN fields)
            TDUnknown → stuck

traverseNormTermF ∷ (Has Context sig m) ⇒ (Vector (Maybe (N Term)) → Term → m (N Term)) → Vector (Maybe (N Term)) → TermF Term → m (N (TermF Term))
traverseNormTermF c locals t0 =
  N <$> case t0 of
    App f a → do
      f' ← c locals f
      a' ← c locals a
      pure $ unN $ postApp f' a'
    Var globalI →
      if globalI < length locals
        then
          pure
            $ let (_, b, potentiallyErasable) = splitAt3 (length locals - 1 - globalI) locals
               in case b of
                    Just (Just v) → unTerm $ unN v
                    _ → Var $ globalI - countErased potentiallyErasable
        else do
          ctx ← get
          let globalAfterErased = globalI - countErased locals
          pure case ctxFindBinding (globalI - length locals) ctx of
            Just (_, _, Just raw, _) → unTerm $ nestedByP raw globalAfterErased
            _ → Var globalAfterErased
    AppErased f _a → unTerm . unN <$> c locals f
    Block (BlockLet _q _name _ty val into) → do
      val' ← c locals val
      unTerm . unN <$> (c (locals |> Just val') $ unLambda into)
    Block (BlockRewrite _prf into) → unTerm . unN <$> c locals into
    Concat a b → case b of
      FRecord b' → unN <$> (concat <$> c locals a <*> c locals b')
      FRow (name, b') → Concat <$> (unN <$> c locals a) <*> (FRow . (name,) . Lambda . unN <$> (c (locals |> Nothing) $ unLambda b'))
    _ → traverseTermF (fmap unN . c locals) (\l → fmap (Lambda . unN) $ c (locals |> Nothing) $ unLambda l) t0
 where
  splitAt3 i v =
    let
      (bef, viewl → aft) = splitAt i v
     in
      (bef, fst <$> aft, maybe [] snd aft)
  countErased = foldl' (\acc e → if isJust e then acc + 1 else acc) 0

normalize' ∷ (Has Context sig m) ⇒ Vector (Maybe (N Term)) → Term → m (N Term)
normalize' locals0 t0 = do
  ctx ← get
  fix
    ( \rec locals →
        unTerm >>> fmap (N . Term . unN) . \case
          ExVar i →
            let (j, depth) = ctxFindEx i ctx
             in traverseNormTermF rec locals (unTerm $ nestedByP j $ depth + length locals)
          x → traverseNormTermF rec locals x
    )
    locals0
    t0

normalize ∷ (Has Context sig m) ⇒ Term → m (N Term)
normalize = normalize' []

applyLambda ∷ N (Lambda Term) → N Term → N Term
applyLambda bod val = runContext $ normalize' [Just val] $ unLambda $ unN bod

-- Rewrites and then simplifies.
-- rewrite :: ∀ m. (Monad m) ⇒ (Term → m (Maybe (N Term))) → Term → m (N Term)
-- rewrite rewriter = fix
-- rewrite ∷ ∀ f via. (Monad f) ⇒ (Term → via → via) → (via → via) → (Term → via → f (Maybe Term)) → via → Term → f Term
-- rewrite onLet onNest rewriter = go
--  where
--   go ∷ via → Term → f Term
--   go via term =
--     rewriter term via >>= \case
--       Just res → pure res
--       Nothing → go' via term

--   go' ∷ via → Term → f Term
--   go' via = \case
--     Block (BlockLet QNorm _ _ val into) → do
--       val' ← go via val
--       go (onLet val' via) $ unLambda into
--     Block (BlockLet QEra _ _ _ into) → go (onLet undefined via) $ unLambda into
--     Block (BlockRewrite _ into) → go via into
--     Lam QNorm arg bod → Lam QNorm arg . Lambda <$> go (onNest via) (unLambda bod)
--     Lam QEra _ bod → go (onLet undefined via) $ unLambda bod
--     AppErased f _ → go via f
--     App f a → do
--       f' ← go via f
--       a' ← go via a
--       pure $ postApp f' a'
--     NumLit x → pure $ NumLit x
--     TagLit x → pure $ TagLit x
--     BoolLit x → pure $ BoolLit x
--     ListLit (Vector' vec) → ListLit . Vector' <$> traverse (go via) vec
--     FieldsLit fi (Vector' vec) → FieldsLit fi . Vector' <$> traverse (bitraverse (go via) (go via)) vec
--     Sorry → pure Sorry
--     Var i → pure $ Var i
--     Builtin x → pure $ Builtin x
--     BuiltinsVar → pure builtinsVar
--     Pi q n inT outT → Pi q n <$> go via inT <*> (Lambda <$> go (onNest via) (unLambda outT))
--     Concat a b → case b of
--       FRecord b' → concat <$> go via a <*> go via b'
--       FRow (i, b') → Concat <$> go via a <*> (FRow . (i,) . Lambda <$> go (onNest via) (unLambda b'))
--     ExVar n i t → ExVar n i <$> go via t
--     UniVar n i t → UniVar n i <$> go via t

-- type Resolved = HashMap ExVarId (Int, Term) -- int for locals
-- type Binding = (Quant, Maybe Ident, Maybe Term, Maybe Term)

-- resolve' ∷ Int → Resolved → Term → Term
-- resolve' _ (HM.null → True) = id
-- resolve' nest exs =
--   runIdentity
--     . rewrite
--       (const (+ 1))
--       (+ 1)
--       ( \term locs → pure $ case term of
--           ExVar _ ex2 _
--             | Just (expectedLocs, val) ← ex2 `HM.lookup` exs →
--                 Just $ nestedBy (locs - expectedLocs) val
--           _ → Nothing
--       )
--       nest

-- resolve ∷ Resolved → Term → Term
-- resolve = resolve' 0

-- runSeqResolve ∷ (Has (Reader (Vector Binding) :+: Writer Resolved) sig m) ⇒ StateC Resolved m a → m a
-- runSeqResolve = runState (\resolved a → tell resolved $> a) mempty

-- withResolved ∷ ((Has (Reader (Vector Binding) :+: Writer Resolved)) sig m) ⇒ (Resolved → m a) → StateC Resolved m a
-- withResolved f = do
--   old ← get
--   let resolveBinds ∷ Vector Binding → Vector Binding
--       resolveBinds = if HM.null old then id else fmap $ bimap id $ fmap (resolve old)
--   (exs, result) ← lift $ listen $ local resolveBinds $ f old
--   put $ old <> exs
--   pure result

-- insertBinds ∷ Binding → Vector Binding → Vector Binding
-- insertBinds (i, nQ, nV, nTy) old = (i, nQ, nested <$> nV, nested <$> nTy) <| (bimap (nested <$>) (nested <$>) <$> old)

-- {- | Checks if two normalized terms are intensionally equivalent.
-- TODO: η-conversion
-- -}
-- isEq' ∷ (Has (Reader (Vector Binding) :+: Writer Resolved) sig m) ⇒ (Maybe Ident → ExVarId → Term → Term → m ()) → Term → Term → m EqRes
-- isEq' f = curry \case
--   (Block{}, _) → undefined
--   (_, Block{}) → undefined
--   (AppErased{}, _) → undefined
--   (_, AppErased{}) → undefined
--   (Lam QEra _ _, _) → undefined
--   (_, Lam QEra _ _) → undefined
--   (ExVar a b c, t) → f a b c t $> EqYes
--   (t, ExVar a b c) → f a b c t $> EqYes
--   (Var a, Var b)
--     | a == b → pure EqYes
--   (Var _, _) → pure EqUnknown
--   (_, Var _) → pure EqUnknown
--   (UniVar _ b1 _, UniVar _ b2 _)
--     | b1 == b2 → pure EqYes
--   (UniVar{}, _) → pure EqUnknown
--   (_, UniVar{}) → pure EqUnknown
--   -- TODO: ExVar? I don't know!
--   (App f1 a1, App f2 a2) →
--     runSeqResolve
--       $ try (withResolved \_ → isEq' f f1 f2)
--       $ try (withResolved \exs → isEq' f (resolve exs a1) (resolve exs a2))
--       $ pure EqYes
--   (App{}, _) → pure EqUnknown
--   (_, App{}) → pure EqUnknown
--   (Sorry, _) → pure EqUnknown
--   (_, Sorry) → pure EqUnknown
--   -- Literals
--   (Lam QNorm i bod1, Lam QNorm _ bod2) → local (insertBinds (QNorm, i, Nothing, Nothing)) $ isEq' f (unLambda bod1) (unLambda bod2)
--   (Lam QNorm _ _, _) → pure EqNot
--   (NumLit a, NumLit b)
--     | a == b → pure EqYes
--   (NumLit _, _) → pure EqNot
--   (TagLit a, TagLit b)
--     | a == b → pure EqYes
--   (TagLit _, _) → pure EqNot
--   (BoolLit a, BoolLit b)
--     | a == b → pure EqYes
--   (BoolLit _, _) → pure EqNot
--   (Builtin a, Builtin b)
--     | a == b → pure EqYes
--   (Builtin _, _) → pure EqNot
--   (_, Builtin _) → pure EqNot
--   (BuiltinsVar, BuiltinsVar) → pure EqYes
--   (BuiltinsVar, _) → pure EqNot
--   (_, BuiltinsVar) → pure EqNot
--   -- TODO: Handle mixed?
--   -- Shame.
--   (Pi q1 i1 inT1 outT1, Pi q2 i2 inT2 outT2)
--     | q1 == q2 → runSeqResolve
--         $ force (withResolved \_ → isEq' f inT1 inT2)
--         $ withResolved \exs →
--           local (insertBinds (QNorm, i1 <|> i2, Nothing, Just $ resolve exs inT1))
--             $ isEq' f (resolve' 1 exs $ unLambda outT1) (resolve' 1 exs $ unLambda outT2)
--   (Pi{}, _) → pure EqNot
--   (Concat _ _, _) → error "TODO isEq Concat"
--   (ListLit (Vector' (viewl → Just (x, xs))), ListLit (Vector' (viewl → Just (y, ys)))) →
--     runSeqResolve
--       $ force (withResolved \_ → isEq' f x y)
--       $ withResolved \exs → isEq' f (ListLit $ Vector' $ resolve exs <$> xs) (ListLit $ Vector' $ resolve exs <$> ys)
--   (ListLit (Vector' (null → True)), ListLit (Vector' (null → True))) → pure EqYes
--   (ListLit _, _) → pure EqNot
--   -- TODO: This is greedy, which is bad. Should uwrap lazily.
--   (FieldsLit f1 (Vector' (viewl → Just ((tagx, x), xs))), FieldsLit f2 (Vector' origY))
--     | f1 == f2 →
--         ifoldr
--           ( \i (tagy, y) rec →
--               runSeqResolve
--                 $ (withResolved \_ → isEq' f tagx tagy)
--                 >>= \case
--                   EqYes → force (withResolved \exs → isEq' f (resolve exs x) (resolve exs y))
--                     $ withResolved \exs →
--                       isEq'
--                         f
--                         (FieldsLit f1 $ Vector' $ bimap (resolve exs) (resolve exs) <$> xs)
--                         (FieldsLit f1 $ Vector' $ bimap (resolve exs) (resolve exs) <$> deleteAt i origY)
--                   EqNot → lift $ rec
--                   EqUnknown → pure EqUnknown
--           )
--           (pure EqNot)
--           origY
--   (FieldsLit f1 (Vector' (null → True)), FieldsLit f2 (Vector' (null → True))) | f1 == f2 → pure EqYes
--   (FieldsLit{}, _) → pure EqNot
--  where
--   -- TODO: FRow???
--   try act cont =
--     act >>= \case
--       EqYes → cont
--       _ → pure EqUnknown
--   force act cont =
--     act >>= \case
--       EqYes → cont
--       x → pure x

-- isEq ∷ Term → Term → EqRes
-- isEq a b =
--   case runIdentity $ runEmpty (pure Nothing) (pure . Just) $ runWriter @Resolved (curry pure) $ runReader @(Vector Binding) [] $ isEq' (\_ _ _ _ → empty) a b of
--     Just (resolved, res) → if HM.null resolved then res else EqUnknown
--     Nothing → EqNot

-- builtinsVar ∷ Term
-- builtinsVar = FieldsLit (FRecord ()) $ Vector' $ (\b → (TagLit $ identOfBuiltin b, Builtin b)) <$> builtinsList

-- data NormCtx
--   = NormBinds !(Vector (Maybe Term))
--   | NormRewrite !Term !Term -- on normalized

-- nestedBy ∷ Int → Term → Term
-- nestedBy by =
--   runIdentity
--     . rewrite
--       (\_ → (+ 1))
--       (+ 1)
--       ( \term locs → case term of
--           Var i | i >= locs → pure $ Just $ Var $ i + by
--           _ → pure Nothing
--       )
--       0

-- nested ∷ Term → Term
-- nested = nestedBy 1

-- normalize' ∷ Int → Vector (Maybe Term) → Term → Term
-- normalize' origLocals origBinds =
--   runIdentity
--     . rewrite
--       (\new (locals, old) → (locals + 1, Just new <| (fmap nested <$> old)))
--       (\(locals, old) → (locals + 1, Nothing <| (fmap nested <$> old)))
--       ( \term (locals, binds) → case term of
--           Var i →
--             pure
--               $ Just
--               $ case binds !? i of
--                 Just (Just val) → val
--                 _ →
--                   let (potentiallyErasableBindings, _) = splitAt (min i locals) binds
--                    in Var $ i - foldl' (\acc x → if isJust x then acc + 1 else acc) 0 potentiallyErasableBindings
--           _ → pure Nothing
--       )
--       (origLocals, origBinds)

-- -- | Fully normalize a term inside of the context.
-- normalize ∷ Vector (Maybe Term) → Term → Term
-- normalize = normalize' 0

-- rewriteTerm ∷ Term → Term → Term → Maybe Term
-- rewriteTerm what0 with0 =
--   runIdentity
--     . runWriter @Any (\(Any rewrote) final → pure $ guard rewrote *> Just final)
--     . rewrite
--       (const (bimap nested nested))
--       (bimap nested nested)
--       ( \term (what, with) → case isEq term what of
--           EqYes → tell (Any True) $> Just with
--           _ → pure Nothing
--       )
--       (what0, with0)

-- {- | Parse builtin
-- Just a variation of parseQQ that has all the builtins in scope from the start.
-- -}
termQQ ∷ QuasiQuoter
termQQ =
  let
    wher ∷ N Term
    wher = N $ Term $ Lam QNorm (Just $ Ident "n" False) $ Lambda $ Term $ Term (Term (Builtin Eq) `App` Term (Var 0)) `App` Term (BoolLit True)
    scope ∷ Vector (Maybe Ident, N Term)
    scope =
      ((\b → (Just $ identOfBuiltin b, N $ Term $ Builtin b)) <$> builtinsList)
        <> [(Just $ Ident "+" True, N $ Term $ Builtin $ Add $ NumDesc False BitsInf), (Just $ Ident "Where" False, wher)]
   in
    QuasiQuoter
      { quoteExp = \s → do
          term ← case parse ((QNorm,) . fst <$> scope) (pack s) of
            Left e → fail $ "termQQ: Parse error: " ++ show e
            Right t → pure t
          let normed = unN $ runContext $ normalize' (Just . snd <$> scope) term
          ⟦normed⟧
      , quotePat = error "termQQ: No pattern support"
      , quoteType = error "termQQ: No type support"
      , quoteDec = error "termQQ: No declaration support"
      }

-- normalizeSource ∷ ByteString → IO ()
-- normalizeSource x = do
--   let t = either (error . show) id $ parse [] x
--   render $ pTerm [] $ normalize [] t

-- normalizeFile ∷ FilePath → IO ()
-- normalizeFile x = normalizeSource =<< readFileBinary x
