module Normalize where

import Control.Algebra
import Control.Carrier.Empty.Church (runEmpty)
import Control.Carrier.Reader (runReader)
import Control.Carrier.State.Church (StateC, runState)
import Control.Carrier.Writer.Church (runWriter)
import Control.Effect.Empty (empty)
import Control.Effect.Reader (Reader, local)
import Control.Effect.State (get, put)
import Control.Effect.Writer (Writer, listen, tell)
import Data.ByteString.Char8 (pack)
import Data.Monoid (Any (..))
import Data.RRBVector (Vector, deleteAt, ifoldr, splitAt, viewl, (!?), (<|))
import Language.Haskell.TH.Quote (QuasiQuoter (..))
import Parser (Bits (..), BlockT (..), BuiltinT (..), ExType (..), ExVarId, Ident (..), Lambda (..), NumDesc (..), Quant (..), TermT (..), Vector' (..), builtinsList, identOfBuiltin, pTerm, parse, recordGet, render)
import RIO hiding (Reader, Vector, ask, concat, drop, force, link, local, replicate, runReader, to, toList, try)
import RIO.HashMap qualified as HM

-- TODO: Erasure is wrong... Verify for \f. f @4

-- | Intensional equality.
data EqRes
  = EqYes -- provably eq
  | EqNot -- provably uneq
  | EqUnknown

type Resolved = HashMap ExVarId TermT
type Binding = (Quant, Ident, Maybe TermT, Maybe TermT)

resolve' ∷ Int → Resolved → TermT → TermT
resolve' _ (HM.null → True) = id
resolve' nest exs =
  runIdentity
    . rewrite
      (const (+ 1))
      (+ 1)
      ( \term locs → pure $ case term of
          ExVar _ ex2 _
            | Just val ← ex2 `HM.lookup` exs →
                Just $ nestedBy locs val
          _ → Nothing
      )
      nest

resolve ∷ Resolved → TermT → TermT
resolve = resolve' 0

runSeqResolve ∷ (Has (Reader (Vector Binding) :+: Writer Resolved) sig m) ⇒ StateC Resolved m a → m a
runSeqResolve = runState (\resolved a → tell resolved $> a) mempty

withResolved ∷ ((Has (Reader (Vector Binding) :+: Writer Resolved)) sig m) ⇒ (Resolved → m a) → StateC Resolved m a
withResolved f = do
  old ← get
  let resolveBinds ∷ Vector Binding → Vector Binding
      resolveBinds = if HM.null old then id else fmap $ bimap id $ fmap (resolve old)
  (exs, result) ← lift $ listen $ local resolveBinds $ f old
  put $ old <> exs
  pure result

insertBinds ∷ Binding → Vector Binding → Vector Binding
insertBinds (i, nQ, nV, nTy) old = (i, nQ, nested <$> nV, nested <$> nTy) <| (bimap (nested <$>) (nested <$>) <$> old)

{- | Checks if two normalized terms are intensionally equivalent.
TODO: η-conversion
-}
isEq' ∷ (Has (Reader (Vector Binding) :+: Writer Resolved) sig m) ⇒ (Ident → ExVarId → ExType → TermT → m ()) → TermT → TermT → m EqRes
isEq' f = curry \case
  (Block{}, _) → undefined
  (_, Block{}) → undefined
  (AppErased{}, _) → undefined
  (_, AppErased{}) → undefined
  (Lam QEra _ _, _) → undefined
  (_, Lam QEra _ _) → undefined
  (ExVar a b c, t) → f a b c t $> EqYes
  (t, ExVar a b c) → f a b c t $> EqYes
  (Var a, Var b)
    | a == b → pure EqYes
  (Var _, _) → pure EqUnknown
  (_, Var _) → pure EqUnknown
  (UniVar _ b1 _, UniVar _ b2 _)
    | b1 == b2 → pure EqYes
  (UniVar{}, _) → pure EqUnknown
  (_, UniVar{}) → pure EqUnknown
  -- TODO: ExVar? I don't know!
  (App f1 a1, App f2 a2) →
    runSeqResolve
      $ try (withResolved \_ → isEq' f f1 f2)
      $ try (withResolved \exs → isEq' f (resolve exs a1) (resolve exs a2))
      $ pure EqYes
  (App{}, _) → pure EqUnknown
  (_, App{}) → pure EqUnknown
  (Sorry, _) → pure EqUnknown
  (_, Sorry) → pure EqUnknown
  -- Literals
  (Lam QNorm i bod1, Lam QNorm _ bod2) → local (insertBinds (QNorm, i, Nothing, Nothing)) $ isEq' f (unLambda bod1) (unLambda bod2)
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
  -- TODO: Handle mixed?
  -- Shame.
  (Pi q1 inT1 (Left (i, outT1)), Pi q2 inT2 (Left (_, outT2)))
    | q1 == q2 → runSeqResolve
        $ force (withResolved \_ → isEq' f inT1 inT2)
        $ withResolved \exs →
          local (insertBinds (QNorm, i, Nothing, Just $ resolve exs inT1))
            $ isEq' f (resolve' 1 exs $ unLambda outT1) (resolve' 1 exs $ unLambda outT2)
  (Pi q1 inT1 (Right outT1), Pi q2 inT2 (Right outT2))
    | q1 == q2 → runSeqResolve
        $ force (withResolved \_ → isEq' f inT1 inT2)
        $ withResolved \exs → isEq' f (resolve exs outT1) (resolve exs outT2)
  (Pi{}, _) → pure EqNot
  (Concat _ _, _) → error "TODO isEq Concat"
  (ListLit (Vector' (viewl → Just (x, xs))), ListLit (Vector' (viewl → Just (y, ys)))) →
    runSeqResolve
      $ force (withResolved \_ → isEq' f x y)
      $ withResolved \exs → isEq' f (ListLit $ Vector' $ resolve exs <$> xs) (ListLit $ Vector' $ resolve exs <$> ys)
  (ListLit (Vector' (null → True)), ListLit (Vector' (null → True))) → pure EqYes
  (ListLit _, _) → pure EqNot
  -- TODO: This is greedy, which is bad. Should uwrap lazily.
  (RecordLit (Vector' (viewl → Just ((tagx, x), xs))), RecordLit (Vector' origY)) →
    ifoldr
      ( \i (tagy, y) rec →
          runSeqResolve
            $ (withResolved \_ → isEq' f tagx tagy)
            >>= \case
              EqYes → force (withResolved \exs → isEq' f (resolve exs x) (resolve exs y))
                $ withResolved \exs → isEq' f (RecordLit $ Vector' $ bimap (resolve exs) (resolve exs) <$> xs) (RecordLit $ Vector' $ bimap (resolve exs) (resolve exs) <$> deleteAt i origY)
              EqNot → lift $ rec
              EqUnknown → pure EqUnknown
      )
      (pure EqNot)
      origY
  (RecordLit (Vector' (null → True)), RecordLit (Vector' (null → True))) → pure EqYes
  (RecordLit _, _) → pure EqNot
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

isEq ∷ TermT → TermT → EqRes
isEq a b =
  case runIdentity $ runEmpty (pure Nothing) (pure . Just) $ runWriter @Resolved (curry pure) $ runReader @(Vector Binding) [] $ isEq' (\_ _ _ _ → empty) a b of
    Just (resolved, res) → if HM.null resolved then res else EqUnknown
    Nothing → EqNot

builtinsVar ∷ TermT
builtinsVar = RecordLit $ Vector' $ (\b → (TagLit $ identOfBuiltin b, Builtin b)) <$> builtinsList
data NormCtx
  = NormBinds !(Vector (Maybe TermT))
  | NormRewrite !TermT !TermT -- on normalized

data ListDropRes = TDFound !(Vector' TermT) | TDMissing | TDUnknown

-- | Produces a non-dependent concat.
concat ∷ TermT → TermT → TermT
concat = curry \case
  (RecordLit l, RecordLit r) → RecordLit $ l <> r
  (l, r) → Concat l $ Right r

unconsField ∷ TermT → Maybe ((TermT, TermT), TermT)
unconsField = \case
  Concat l (Right (Concat m (Right r))) → unconsField $ concat l $ concat m r
  Concat (RecordLit (Vector' fi)) (Right r) → case viewl fi of
    Just (x, xs) → Just (x, concat (RecordLit $ Vector' xs) r)
    Nothing → unconsField r
  RecordLit (Vector' fi) → case viewl fi of
    Just (x, xs) → Just (x, RecordLit $ Vector' xs)
    Nothing → Nothing
  _ → Nothing

repeat ∷ Integer → (a → a) → a → a
repeat n f = case n of
  0 → id
  _ → f . repeat (n - 1) f

-- TODO: Really simple, expand upon.
unplus ∷ TermT → (Maybe TermT, Integer)
unplus (NumLit n) | n >= 0 = (Nothing, n)
unplus (Builtin (Add (NumDesc True BitsInf)) `App` a `App` NumLit n) = (+ n) <$> unplus a
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

-- | Processes application of `f` onto `a`.
postApp ∷ TermT → TermT → TermT
postApp = curry \case
  (Lam QNorm _ bod, a) → applyLambda bod a
  (App (Builtin RecordGet) name1, a) →
    let
      search a' = case unconsField a' of
        Nothing → recordGet name1 a'
        Just ((name2, v), rest) → case isEq name1 name2 of
          EqYes → v
          EqNot → search rest
          EqUnknown → recordGet name1 a'
     in
      search a
  (Builtin RecordKeepFields `App` ListLit tags, a) → RecordLit $ (\tag → (tag, recordGet tag a)) <$> tags
  (Builtin RecordDropFields `App` ListLit tags, a) → recordDropFields tags a
  (Builtin ListLength, ListLit (Vector' fi)) → NumLit $ fromIntegral $ length fi
  (f@(Builtin ListIndexL `App` ListLit (Vector' vals) `App` NumLit i), a) → case vals !? fromIntegral i of
    Just v → v
    Nothing → App f a
  (Builtin NatFold `App` start `App` step, n) →
    let
      (nTM, nV) = unplus n
     in
      -- TODO: causes constant re-normalization of `int+_fold` args.
      (if nV > 0 then normalize [] else id)
        $ repeat nV (App step)
        $ case nTM of
          Nothing → start
          Just nT → Builtin NatFold `App` start `App` step `App` nT
  (Builtin If `App` (BoolLit cond) `App` thenBranch, elseBranch) →
    if cond
      then normalize [Just $ RecordLit []] thenBranch
      else normalize [Just $ RecordLit []] elseBranch
  (Builtin IntGte0, NumLit x) → BoolLit $ x >= 0
  (Builtin IntEq `App` (NumLit l), NumLit r) → BoolLit $ l == r
  (Builtin IntNeq `App` (NumLit l), NumLit r) → BoolLit $ l /= r
  (Builtin Wrap `App` _ty, b) → b
  (Builtin Unwrap `App` _ty, b) → b
  -- Add
  (Builtin (Add d) `App` a, NumLit b)
    | b == 0 → a
    | NumLit a' ← a → NumLit $ numDecDispatch d (\(_ ∷ Proxy x) → fromIntegral @x $ fromIntegral a' + fromIntegral b) (\_ → a' + b)
  -- Sub
  (Builtin (Sub d) `App` a, NumLit b)
    | b == 0 → a
    | NumLit a' ← a → NumLit $ numDecDispatch d (\(_ ∷ Proxy x) → fromIntegral @x $ fromIntegral a' + fromIntegral b) \_ → undefined
  (Builtin IntNeg, NumLit x) → NumLit $ -x
  (f, a) → App f a
 where
  -- Drop `x` from ListLit.
  listLitDrop ∷ TermT → Vector' TermT → ListDropRes
  listLitDrop x (Vector' fi) =
    ifoldr
      ( \i n rec → case isEq x n of
          EqYes → TDFound $ Vector' $ deleteAt i fi
          EqNot → rec
          EqUnknown → TDUnknown
      )
      TDMissing
      fi

  recordDropFields ∷ Vector' TermT → TermT → TermT
  recordDropFields tags fields0 = case tags of
    Vector' (null → True) → RecordLit []
    _ →
      let
        stuck = App (App (Builtin RecordDropFields) $ ListLit tags) fields0
       in
        case unconsField fields0 of
          Nothing → stuck
          Just ((n, v), fields) → case listLitDrop n tags of
            TDFound tags' → recordDropFields tags' fields
            TDMissing →
              concat (RecordLit [(n, v)]) $ recordDropFields tags fields
            TDUnknown → stuck

-- Erases, rewrites & simplifies. In that order. Doesn't rewrite the simplified result.
rewrite ∷ ∀ f via. (Monad f) ⇒ (TermT → via → via) → (via → via) → (TermT → via → f (Maybe TermT)) → via → TermT → f TermT
rewrite onLet onNest rewriter = go
 where
  go ∷ via → TermT → f TermT
  go via term =
    rewriter term via >>= \case
      Just res → pure res
      Nothing → go' via term

  go' ∷ via → TermT → f TermT
  go' via = \case
    Block (BlockLet QNorm _ _ val into) → do
      val' ← go via val
      go (onLet val' via) $ unLambda into
    Block (BlockLet QEra _ _ _ into) → go (onLet undefined via) $ unLambda into
    Block (BlockRewrite _ into) → go via into
    Lam QNorm arg bod → Lam QNorm arg . Lambda <$> go (onNest via) (unLambda bod)
    Lam QEra _ bod → go (onLet undefined via) $ unLambda bod
    AppErased f _ → go via f
    App f a → do
      f' ← go via f
      a' ← go via a
      pure $ postApp f' a'
    NumLit x → pure $ NumLit x
    TagLit x → pure $ TagLit x
    BoolLit x → pure $ BoolLit x
    ListLit (Vector' vec) → ListLit . Vector' <$> traverse (go via) vec
    RecordLit (Vector' vec) → RecordLit . Vector' <$> traverse (bitraverse (go via) (go via)) vec
    Sorry → pure Sorry
    Var i → pure $ Var i
    Builtin x → pure $ Builtin x
    BuiltinsVar → pure builtinsVar
    Pi q inT outT → do
      inT' ← go via inT
      outT' ← case outT of
        Left (n, x) → Left . (n,) . Lambda <$> go (onNest via) (unLambda x)
        Right x → Right <$> go via x
      pure $ Pi q inT' outT'
    Concat a b → do
      a' ← go via a
      b' ← either (\(n, b') → Left . (n,) . Lambda <$> go (onNest via) (unLambda b')) (fmap Right . go via) b
      pure $ case (a', b') of
        (RecordLit a'', Right (RecordLit b'')) → RecordLit $ a'' <> b''
        _ → Concat a' b'
    ExVar n i t →
      ExVar n i <$> case t of
        ExType t' → ExType <$> go via t'
        ExSuperType → pure ExSuperType
    UniVar n i t → UniVar n i <$> go via t

nestedBy ∷ Int → TermT → TermT
nestedBy by =
  runIdentity
    . rewrite
      (\_ → (+ 1))
      (+ 1)
      ( \term locs → case term of
          Var i | i >= locs → pure $ Just $ Var $ i + by
          _ → pure Nothing
      )
      0

nested ∷ TermT → TermT
nested = nestedBy 1

normalize' ∷ Int → Vector (Maybe TermT) → TermT → TermT
normalize' origLocals origBinds =
  runIdentity
    . rewrite
      (\new (locals, old) → (locals + 1, Just new <| (fmap nested <$> old)))
      (\(locals, old) → (locals + 1, Nothing <| (fmap nested <$> old)))
      ( \term (locals, binds) → case term of
          Var i →
            pure
              $ Just
              $ case binds !? i of
                Just (Just val) → val
                _ →
                  let (potentiallyErasableBindings, _) = splitAt (min i locals) binds
                   in Var $ i - foldl' (\acc x → if isJust x then acc + 1 else acc) 0 potentiallyErasableBindings
          _ → pure Nothing
      )
      (origLocals, origBinds)

-- | Fully normalize a term inside of the context.
normalize ∷ Vector (Maybe TermT) → TermT → TermT
normalize = normalize' 0

rewriteTerm ∷ TermT → TermT → TermT → Maybe TermT
rewriteTerm what0 with0 =
  runIdentity
    . runWriter @Any (\(Any rewrote) final → pure $ guard rewrote *> Just final)
    . rewrite
      (const (bimap nested nested))
      (bimap nested nested)
      ( \term (what, with) → case isEq term what of
          EqYes → tell (Any True) $> Just with
          _ → pure Nothing
      )
      (what0, with0)

applyLambda ∷ Lambda TermT → TermT → TermT
applyLambda bod val = normalize' 1 [Just val] $ unLambda bod

{- | Parse builtin
Just a variation of parseQQ that has all the builtins in scope from the start.
-}
termQQ ∷ QuasiQuoter
termQQ =
  let
    wher = Lam QNorm (Ident "n" False) $ Lambda $ Builtin Eq `App` BoolLit True `App` Var 0
    scope =
      ((\b → (identOfBuiltin b, Builtin b)) <$> builtinsList)
        <> [(Ident "+" True, Builtin $ Add $ NumDesc False BitsInf), (Ident "++" True, Builtin $ Add $ NumDesc True BitsInf), (Ident "Where" False, wher)]
   in
    QuasiQuoter
      { quoteExp = \s → do
          term ← case parse ((QNorm,) . fst <$> scope) (pack s) of
            Left e → fail $ "termQQ: Parse error: " ++ show e
            Right t → pure t
          let normed = normalize (Just . snd <$> scope) term
          ⟦normed⟧
      , quotePat = error "termQQ: No pattern support"
      , quoteType = error "termQQ: No type support"
      , quoteDec = error "termQQ: No declaration support"
      }

normalizeSource ∷ ByteString → IO ()
normalizeSource x = do
  let t = either (error . show) id $ parse [] x
  render $ pTerm (0, []) $ normalize [] t

normalizeFile ∷ FilePath → IO ()
normalizeFile x = normalizeSource =<< readFileBinary x
