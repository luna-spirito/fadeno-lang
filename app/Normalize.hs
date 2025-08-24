module Normalize where

import Control.Algebra
import Control.Carrier.Empty.Church (runEmpty)
import Control.Carrier.State.Church (StateC, evalState)
import Control.Carrier.Writer.Church (WriterC, runWriter)
import Control.Effect.Empty (empty)
import Control.Effect.State (State, get, modify)
import Control.Effect.Writer (tell)
import Data.ByteString.Char8 (pack)
import Data.Monoid (Any (..))
import Data.RRBVector (Vector, deleteAt, findIndexL, ifoldr, splitAt, viewl, viewr, zip, (!?), (|>))
import Language.Haskell.TH.Quote (QuasiQuoter (..))
import Parser (Bits (..), BlockF (..), BuiltinT (..), Fields (..), Ident (..), Lambda (..), NumDesc (..), Quant (..), Term (..), TermF (..), Vector' (..), builtinsList, identOfBuiltin, intercept, nestedByP, nestedByP', pTerm, parse, recordGet, render, traverseTermF)
import RIO hiding (Reader, Vector, ask, concat, drop, force, link, local, replicate, runReader, to, toList, try, zip)

-- TODO: Erasure is wrong... Verify for \f. f @4

-- Like Throw/Catch, but doesn't abort the computation.
-- More of crutch I guess...
data Isolate m a where
  Isolate ∷ m a → m a → Isolate m a
  Infect ∷ Isolate m ()
newtype IsolateC m a = IsolateC {unIsolateC ∷ WriterC Any m a}
  deriving (Functor, Applicative, Monad)
runIsolate ∷ (Applicative m) ⇒ IsolateC m a → m a
runIsolate (IsolateC act) = runWriter (\_ → pure) act

instance (Algebra sig m) ⇒ Algebra (Isolate :+: sig) (IsolateC m) where
  alg hdl sig ctx = IsolateC case sig of
    L (Isolate act err) → do
      (Any infected, res) ← intercept @Any $ unIsolateC $ hdl $ act <$ ctx
      if infected
        then unIsolateC $ hdl $ err <$ ctx
        else pure res
    L Infect → tell (Any True) $> ctx
    R other → alg (unIsolateC . hdl) (R other) ctx

type Binding = (Quant, Maybe Ident, Maybe Term, Term)
newtype Epoch = Epoch Int deriving (Show, Eq)
data Scopes = Scopes !(Vector Binding) !(Vector (Epoch, Vector EEntry))

data Dyn = Dyn !Epoch !Term
data EEntry = EMarker | EVar !Int !(Either (Int, Term) Term) | EUniVar !Int deriving (Eq, Show)
type Context = State Scopes :+: Isolate

runContext' ∷ (Applicative m) ⇒ StateC Scopes m a → m a
runContext' = evalState (Scopes [] [(Epoch 0, [])])

withBinding ∷ (Has Context sig m) ⇒ Binding → m a → m a
withBinding b act = do
  modify @Scopes \(Scopes bs es) → Scopes (bs |> b) (es |> (Epoch 0, []))
  res ← act
  modify @Scopes \(Scopes bs es) →
    Scopes
      (maybe (error "Missing binding") fst $ viewr bs)
      (maybe (error "Missing ex scope") fst $ viewr es)
  pure res

-- | Intensional equality.
data EqRes
  = EqYes -- provably eq
  | EqNot -- provably uneq
  | EqUnknown

getScopeId ∷ (Has Context sig m) ⇒ m Int
getScopeId = (\(Scopes bs _es) → length bs) <$> get @Scopes

getEpoch ∷ (Has Context sig m) ⇒ m Epoch
getEpoch = maybe (error "Missing ex scope") (fst . snd) . (\(Scopes _ es) → viewr es) <$> get @Scopes

-- unwrap :: (Has Context sig m) ⇒ Term → m (TermF Dyn)
-- unwrap = traverseTermF dyn (fmap Lambda . dyn . unLambda) . unTerm
dyn ∷ (Has Context sig m) ⇒ Term → m Dyn
dyn x = (`Dyn` x) <$> getEpoch

fDyn ∷ Epoch → Term → TermF Dyn
fDyn e = run . traverseTermF (pure . Dyn e) (pure . Lambda . Dyn e . unLambda) . unTerm

-- | Unwraps a term that contains existentials
fetchWith ∷ (Has Context sig m) ⇒ (Term → m Term) → Dyn → m Term
fetchWith f (Dyn objEpoch x) = do
  epoch ← getEpoch
  if epoch == objEpoch
    then pure x
    else f x

--
fetchT ∷ (Has Context sig m) ⇒ Dyn → m Term
fetchT = fetchWith normalize

fetchLambda ∷ (Has Context sig m) ⇒ Lambda Dyn → m (Lambda Term)
fetchLambda = fmap Lambda . fetchWith (normalize' [Nothing]) . unLambda

isEq' ∷ (Has Context sig m) ⇒ ((Int, Int) → Term → m ()) → Term → Term → m EqRes
isEq' f = \l0 r0 →
  send
    $ Isolate
      ( go l0 r0 >>= \case
          EqYes → pure EqYes
          x → send Infect *> pure x
      )
      (pure EqNot)
 where
  go l0 r0 =
    getEpoch >>= \e0 → case (fDyn e0 l0, fDyn e0 r0) of
      (Block{}, _) → undefined
      (_, Block{}) → undefined
      (AppErased{}, _) → undefined
      (_, AppErased{}) → undefined
      (Lam QEra _ _, _) → undefined
      (_, Lam QEra _ _) → undefined
      (BuiltinsVar, _) → undefined
      (_, BuiltinsVar) → undefined
      (ExVar i, _) → f i r0 $> EqYes
      (_, ExVar i) → f i l0 $> EqYes
      (Var a, Var b)
        | a == b → pure EqYes
      (Var _, _) → pure EqUnknown
      (_, Var _) → pure EqUnknown
      (UniVar i1 _, UniVar i2 _)
        | i1 == i2 → pure EqYes
      (UniVar{}, _) → pure EqUnknown
      (_, UniVar{}) → pure EqUnknown
      (App f1 a1, App f2 a2) →
        try (isEqD (fetchT f1) (fetchT f2))
          $ try (isEqD (fetchT a1) (fetchT a2))
          $ pure EqYes
      (App{}, _) → pure EqUnknown
      (_, App{}) → pure EqUnknown
      (Sorry, _) → pure EqUnknown
      (_, Sorry) → pure EqUnknown
      -- Literals
      (Lam QNorm i bod1, Lam QNorm _ bod2) →
        withBinding (QNorm, i, Nothing, Term $ Builtin Any')
          $ isEqD (unLambda <$> fetchLambda bod1) (unLambda <$> fetchLambda bod2)
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
      (Pi q1 i1 inT1 outT1, Pi q2 i2 inT2 outT2)
        | q1 == q2 →
            force (isEqD (fetchT inT1) (fetchT inT2)) do
              inT1' ← fetchT inT1
              withBinding (QNorm, i1 <|> i2, Nothing, inT1') $ isEqD (unLambda <$> fetchLambda outT1) (unLambda <$> fetchLambda outT2)
      (Pi{}, _) → pure EqNot
      (Concat _ _, _) → error "TODO isEq Concat"
      (ListLit (Vector' as), ListLit (Vector' bs)) →
        if length as /= length bs
          then pure EqNot
          else foldr (\(a, b) next → force (isEqD (fetchT a) (fetchT b)) next) (pure EqYes) (zip as bs)
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
                            isEqD (fetchT tag1) (fetchT tag2) >>= \case
                              EqYes → force (isEqD (fetchT val1) (fetchT val2)) $ recO $ deleteAt i bs
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
  isEqD a b = uncurry go =<< ((,) <$> a <*> b)
  -- TODO: FRow???
  try act cont =
    act >>= \case
      EqYes → cont
      _ → pure EqUnknown
  force act cont =
    act >>= \case
      EqYes → cont
      x → pure x

isEq ∷ Term → Term → EqRes
isEq a b = run $ runIsolate $ runContext' $ runEmpty (pure EqUnknown) pure $ isEq' (\_ _ → empty) a b

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

repeat ∷ Integer → (a → a) → a → a
repeat n f = case n of
  0 → id
  _ → f . repeat (n - 1) f

-- TODO: Really simple, expand upon.
unplus ∷ Term → (Maybe Term, Integer)
unplus (unTerm → NumLit n) | n >= 0 = (Nothing, n)
unplus (unTerm → (Term (Term (Builtin (Add (NumDesc True BitsInf))) `App` a) `App` Term (NumLit n))) = (+ n) <$> unplus a
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
postApp ∷ Term → Term → Term
postApp f0 a0 = case (unTerm f0, a0) of
  (Lam QNorm _ bod, a) → applyLambda bod a
  (App (Term (Builtin RecordGet)) name1, a) →
    let
      search a' = case unconsField a' of
        Nothing → recordGet name1 a'
        Just ((name2, v), rest) → case isEq name1 name2 of
          EqYes → v
          EqNot → search rest
          EqUnknown → recordGet name1 a'
     in
      search a
  (Term (Builtin RecordKeepFields) `App` Term (ListLit tags), a) → Term . FieldsLit (FRecord ()) $ (\tag → (tag, recordGet tag a)) <$> tags
  (Term (Builtin RecordDropFields) `App` Term (ListLit tags), a) → recordDropFields tags a
  (Builtin ListLength, Term (ListLit (Vector' fi))) → Term $ NumLit $ fromIntegral $ length fi
  (f@(Term (Term (Builtin ListIndexL) `App` Term (ListLit (Vector' vals))) `App` Term (NumLit i)), a) → case vals !? fromIntegral i of
    Just v → v
    Nothing → Term $ App (Term f) a
  (Term (Term (Builtin NatFold) `App` start) `App` step, n) →
    let
      (nTM, nV) = unplus n
     in
      -- TODO: causes constant re-normalization of `int+_fold` args.
      (if nV > 0 then run . runIsolate . runContext' . normalize else id)
        $ repeat nV (Term . App step)
        $ case nTM of
          Nothing → start
          Just nT → Term $ Term (Term (Term (Builtin NatFold) `App` start) `App` step) `App` nT
  (Term (Term (Builtin If) `App` (Term (BoolLit cond))) `App` thenBranch, elseBranch) →
    if cond then thenBranch else elseBranch
  (Builtin IntGte0, Term (NumLit x)) → Term $ BoolLit $ x >= 0
  (Term (Builtin IntEq) `App` Term (NumLit l), Term (NumLit r)) → Term $ BoolLit $ l == r
  (Term (Builtin IntNeq) `App` Term (NumLit l), Term (NumLit r)) → Term $ BoolLit $ l /= r
  (Term (Builtin Wrap) `App` _ty, b) → b
  (Term (Builtin Unwrap) `App` _ty, b) → b
  -- Add
  (Term (Builtin (Add d)) `App` a, Term (NumLit b))
    | b == 0 → a
    | Term (NumLit a') ← a → Term $ NumLit $ numDecDispatch d (\(_ ∷ Proxy x) → fromIntegral @x $ fromIntegral a' + fromIntegral b) (\_ → a' + b)
  -- Sub
  (Builtin (IntNeg d), Term (NumLit x)) → Term $ NumLit $ numDecDispatch d (\(_ ∷ Proxy x) → fromIntegral @x $ -fromIntegral x) (\_ → -x)
  (f, a) → Term $ App (Term f) a
 where
  -- Drop `x` from ListLit.
  listLitDrop ∷ Term → Vector' Term → ListDropRes
  listLitDrop x (Vector' fi) =
    ifoldr
      ( \i n rec → case isEq x n of
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
        case unconsField fields0 of
          Nothing → stuck
          Just ((n, v), fields) → case listLitDrop n tags of
            TDFound tags' → recordDropFields tags' fields
            TDMissing →
              concat (Term $ FieldsLit (FRecord ()) [(n, v)]) $ recordDropFields tags fields
            TDUnknown → stuck

splitAt3 ∷ Int → Vector a → (Vector a, Maybe a, Vector a)
splitAt3 i v =
  let
    (bef, viewl → aft) = splitAt i v
   in
    (bef, fst <$> aft, maybe [] snd aft)

traverseNormTermF ∷ (Has Context sig m) ⇒ (Vector (Maybe Term) → Term → m Term) → Vector (Maybe Term) → TermF Term → m Term
traverseNormTermF c locals t0 =
  case t0 of
    BuiltinsVar → pure builtinsVar
    Lam QEra _ body → c (locals |> Just undefined) $ unLambda body -- TODO: Total?
    App f a → do
      f' ← c locals f
      a' ← c locals a
      pure $ postApp f' a'
    Var globalI →
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
          Scopes globals _ ← get @Scopes
          let updatedGlobalI = globalI - countErased locals
          pure case globals !? (length globals - 1 - (globalI - length locals)) of
            Just (_, _, Just raw, _) → nestedByP raw $ updatedGlobalI
            _ → Term $ Var updatedGlobalI
    AppErased f _a → c locals f
    Block (BlockLet _q _name _ty val into) → do
      val' ← c locals val
      c (locals |> Just val') $ unLambda into
    Block (BlockRewrite _prf into) → c locals into
    Concat a b → case b of
      FRecord b' → concat <$> c locals a <*> c locals b'
      FRow (name, b') → Term <$> (Concat <$> c locals a <*> (FRow . (name,) . Lambda <$> (c (locals |> Nothing) $ unLambda b')))
    ExVar (i, subi) → do
      Scopes globals exs ← get @Scopes
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
    _ → Term <$> traverseTermF (c locals) (\l → fmap Lambda $ c (locals |> Nothing) $ unLambda l) t0
 where
  countErased = foldl' (\acc e → if isJust e then acc + 1 else acc) 0

builtinsVar ∷ Term
builtinsVar = Term $ FieldsLit (FRecord ()) $ Vector' $ (\b → (Term $ TagLit $ identOfBuiltin b, Term $ Builtin b)) <$> builtinsList

rewrite ∷ (Has Context sig m) ⇒ (Int → Term → m (Maybe Term)) → Vector (Maybe Term) → Term → m Term
rewrite rewriter = fix \rec locals t →
  rewriter (length locals) t >>= \case
    Just u → pure u
    Nothing → traverseNormTermF rec locals $ unTerm t

normalize' ∷ (Has Context sig m) ⇒ Vector (Maybe Term) → Term → m Term
normalize' = rewrite (\_ _ → pure Nothing)

normalize ∷ (Has Context sig m) ⇒ Term → m Term
normalize = normalize' []

applyLambda ∷ Lambda Term → Term → Term
applyLambda bod val = run $ runContext' $ runIsolate $ normalize' [Just val] $ unLambda bod

rewriteTerm ∷ (Has Context sig m) ⇒ Term → Term → Term → m (Maybe Term)
rewriteTerm what0 with0 =
  runWriter @Any (\(Any rewrote) final → pure $ guard rewrote *> Just final)
    . rewrite
      ( \locs term → case isEq term (nestedByP what0 locs) of
          EqYes → tell (Any True) $> Just (nestedByP with0 locs)
          _ → pure Nothing
      )
      []

-- {- | Parse builtin
-- Just a variation of parseQQ that has all the builtins in scope from the start.
-- -}
termQQ ∷ QuasiQuoter
termQQ =
  let
    wher ∷ Term
    wher = Term $ Lam QNorm (Just $ Ident "n" False) $ Lambda $ Term $ Term (Term (Builtin Eq) `App` Term (Var 0)) `App` Term (BoolLit True)
    scope ∷ Vector (Maybe Ident, Term)
    scope =
      ((\b → (Just $ identOfBuiltin b, Term $ Builtin b)) <$> builtinsList)
        <> [(Just $ Ident "+" True, Term $ Builtin $ Add $ NumDesc False BitsInf), (Just $ Ident "Where" False, wher)]
   in
    QuasiQuoter
      { quoteExp = \s → do
          term ← case parse ((QNorm,) . fst <$> scope) (pack s) of
            Left e → fail $ "termQQ: Parse error: " ++ show e
            Right t → pure t
          let normed = run $ runIsolate $ runContext' $ normalize' (Just . snd <$> scope) term
          ⟦normed⟧
      , quotePat = error "termQQ: No pattern support"
      , quoteType = error "termQQ: No type support"
      , quoteDec = error "termQQ: No declaration support"
      }

normalizeSource ∷ ByteString → IO ()
normalizeSource x = do
  let t = either (error . show) id $ parse [] x
  render $ pTerm [] $ run $ runIsolate $ runContext' $ normalize t

normalizeFile ∷ FilePath → IO ()
normalizeFile x = normalizeSource =<< readFileBinary x
