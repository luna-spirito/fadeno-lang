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
import Data.RRBVector (Vector, deleteAt, ifoldr, splitAt, viewl, (!?), (<|))
import Language.Haskell.TH.Quote (QuasiQuoter (..))
import Parser (BlockT (..), BuiltinT (..), ExType (..), ExVarId, Ident (..), Lambda (..), OpT (..), Quant (..), TermT (..), Vector' (..), builtinsList, identOfBuiltin, pTerm', parse, parseFile, recordGet, render)
import RIO hiding (Reader, Vector, ask, concat, drop, force, link, local, replicate, runReader, to, toList, try)
import RIO.HashMap qualified as HM

-- TODO: Erasure is wrong... Verify for \f. f @4

-- | Intensional equality.
data EqRes
  = EqYes -- provably eq
  | EqNot -- provably uneq
  | EqUnknown

type Resolved = HashMap ExVarId TermT
type Binding = (Quant, Maybe TermT, Maybe TermT)

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
insertBinds (nQ, nV, nTy) old = (nQ, nested <$> nV, nested <$> nTy) <| (bimap (nested <$>) (nested <$>) <$> old)

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
  (Var a, Var b)
    | a == b → pure EqYes
  (Var _, _) → pure EqUnknown
  (_, Var _) → pure EqUnknown
  (ExVar a b c, t) → f a b c t $> EqYes
  (t, ExVar a b c) → f a b c t $> EqYes
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
  (Op a1 op1 b1, Op a2 op2 b2)
    | op1 == op2 → runSeqResolve
        $ try (withResolved \_ → isEq' f a1 a2)
        $ withResolved \exs → isEq' f (resolve exs b1) (resolve exs b2)
  (Op{}, _) → pure EqUnknown
  (_, Op{}) → pure EqUnknown
  (Sorry _ a, b) → isEq' f a b
  (a, Sorry _ b) → isEq' f a b
  -- Literals
  (Lam QNorm _ bod1, Lam QNorm _ bod2) → local (insertBinds (QNorm, Nothing, Nothing)) $ isEq' f (unLambda bod1) (unLambda bod2)
  (Lam QNorm _ _, _) → pure EqNot
  (NatLit a, NatLit b)
    | a == b → pure EqYes
  (NatLit _, _) → pure EqNot
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
  (Pi q1 inT1 (Left (_, outT1)), Pi q2 inT2 (Left (_, outT2)))
    | q1 == q2 → runSeqResolve
        $ force (withResolved \_ → isEq' f inT1 inT2)
        $ withResolved \exs →
          local (insertBinds (QNorm, Nothing, Just $ resolve exs inT1))
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

repeat ∷ Word32 → (a → a) → a → a
repeat n f = case n of
  0 → id
  _ → f . repeat (n - 1) f

-- TODO: Really simple, expand upon.
unplus ∷ TermT → (Maybe TermT, Word32)
unplus (NatLit n) = (Nothing, n)
unplus (Op a Add (NatLit n)) = (Just a, n)
unplus x = (Just x, 0)

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
  (Builtin ListLength, ListLit (Vector' fi)) → NatLit $ fromIntegral $ length fi
  (f@(Builtin ListIndexL `App` ListLit (Vector' vals) `App` NatLit i), a) → case vals !? fromIntegral i of
    Just v → v
    Nothing → App f a
  (Builtin NatFold `App` start `App` step, n) →
    let
      (nTM, nV) = unplus n
     in
      -- TODO: causes constant re-normalization of `nat~fold` args.
      (if nV > 0 then normalize [] else id)
        $ repeat nV (App step)
        $ case nTM of
          Nothing → start
          Just nT → Builtin NatFold `App` start `App` step `App` nT
  (Builtin If `App` (BoolLit cond) `App` thenBranch, elseBranch) →
    if cond
      then normalize [Just $ RecordLit []] thenBranch
      else normalize [Just $ RecordLit []] elseBranch
  (Builtin ULte `App` (NatLit l), NatLit r) → BoolLit $ l <= r
  (Builtin ULt `App` (NatLit l), NatLit r) → BoolLit $ l < r
  (Builtin UEq `App` (NatLit l), NatLit r) → BoolLit $ l == r
  (Builtin UNeq `App` (NatLit l), NatLit r) → BoolLit $ l /= r
  (Builtin Wrap `App` _ty, b) → b
  (Builtin Unwrap `App` _ty, b) → b
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
    Block (BlockRewrite from to) → error "TODO rewrite BlockRewrite"
    Lam QNorm arg bod → Lam QNorm arg . Lambda <$> go (onNest via) (unLambda bod)
    Lam QEra _ bod → go (onLet undefined via) $ unLambda bod
    Op aT op bT → do
      aT' ← go via aT
      bT' ← go via bT
      pure $ case (aT', bT') of
        (NatLit a, NatLit b) → NatLit $ case op of
          Add → a + b
          Sub → a - b
          Mul → a * b
          Div → a `div` b
        _ → Op aT' op bT'
    AppErased f _ → go via f
    App f a → do
      f' ← go via f
      a' ← go via a
      pure $ postApp f' a'
    NatLit x → pure $ NatLit x
    TagLit x → pure $ TagLit x
    BoolLit x → pure $ BoolLit x
    ListLit (Vector' vec) → ListLit . Vector' <$> traverse (go via) vec
    RecordLit (Vector' vec) → RecordLit . Vector' <$> traverse (bitraverse (go via) (go via)) vec
    Sorry n x → Sorry n <$> go via x
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

normalize ∷ Vector (Maybe TermT) → TermT → TermT
normalize origBinds =
  runIdentity
    . rewrite
      (\new old → Just new <| (fmap nested <$> old))
      (\old → Nothing <| (fmap nested <$> old))
      ( \term binds → case term of
          Var i →
            pure
              $ Just
              $ let (before, after) = splitAt i binds
                 in case after of
                      (viewl → Just (Just val, _)) → val
                      _ → Var $ i - foldl' (\acc x → if isJust x then acc + 1 else acc) 0 before
          _ → pure Nothing
      )
      origBinds

rewriteTerm ∷ TermT → TermT → TermT → TermT
rewriteTerm what0 with0 =
  runIdentity
    . rewrite
      (const (bimap nested nested))
      (bimap nested nested)
      ( \term (what, with) → pure $ case isEq term what of
          EqYes → Just with
          _ → Nothing
      )
      (what0, with0)

applyLambda ∷ Lambda TermT → TermT → TermT
applyLambda bod val = normalize [Just val] $ unLambda bod

{- | Parse builtin
Just a variation of parseQQ that has all the builtins in scope from the start.
-}
termQQ ∷ QuasiQuoter
termQQ =
  let
    wher = Lam QNorm (Ident "n" False) $ Lambda $ Builtin Eq `App` (Var 0) `App` BoolLit True
    scope = ((\b → (identOfBuiltin b, Builtin b)) <$> builtinsList) <> [(Ident "Where" False, wher)]
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

normalizeFile ∷ FilePath → IO ()
normalizeFile x = do
  t ← parseFile x
  render $ pTerm' $ normalize [] t
