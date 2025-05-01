module Normalize where

import Data.RRBVector (Vector, deleteAt, drop, ifoldr, viewl, (|>))
import GHC.Exts (IsList (..))
import Language.Haskell.TH.Quote (QuasiQuoter (..))
import Parser (BlockT (..), BuiltinT (..), Lambda (..), OpT (..), TermT (..), Vector' (..), builtinsList, identOfBuiltin, pTerm', parseFile, parseQQ, recordGet, render)
import RIO hiding (Reader, Vector, ask, drop, link, local, replicate, runReader, to, toList)

-- | Intensional equality.
data EqRes
  = EqYes -- provably eq
  | EqNot -- provably uneq
  | EqUnknown

{- | Checks if two normalized terms are intensionally equivalent.
TODO: η-conversion
-}
isEq ∷ TermT → TermT → EqRes
isEq = curry \case
  (Block{}, _) → undefined
  (_, Block{}) → undefined
  (Var a, Var b)
    | a == b → EqYes
  (Var _, _) → EqUnknown
  (_, Var _) → EqUnknown
  (UniVar _ b1 _, UniVar _ b2 _)
    | b1 == b2 → EqYes
  (UniVar{}, _) → EqUnknown
  (_, UniVar{}) → EqUnknown
  -- TODO: ExVar? I don't know!
  (ExVar{}, _) → error "TODO"
  (_, ExVar{}) → error "TODO"
  (App f1 a1, App f2 a2) → tryEq f1 f2 $ tryEq a1 a2 $ EqYes
  (App{}, _) → EqUnknown
  (_, App{}) → EqUnknown
  (Op a1 op1 b1, Op a2 op2 b2)
    | op1 == op2 → tryEq a1 a2 $ tryEq b1 b2 $ EqYes
  (Op{}, _) → EqUnknown
  (_, Op{}) → EqUnknown
  (Sorry _ a, b) → isEq a b
  (a, Sorry _ b) → isEq a b
  -- Literals
  (Lam _ bod1, Lam _ bod2) → isEq (unLambda bod1) (unLambda bod2)
  (Lam _ _, _) → EqNot
  (NatLit a, NatLit b)
    | a == b → EqYes
  (NatLit _, _) → EqNot
  (TagLit a, TagLit b)
    | a == b → EqYes
  (TagLit _, _) → EqNot
  (BoolLit a, BoolLit b)
    | a == b → EqYes
  (BoolLit _, _) → EqNot
  (Quantification q1 _n1 k1 t1, Quantification q2 _n2 k2 t2)
    | q1 == q2 → forceEq k1 k2 $ isEq (unLambda t1) (unLambda t2)
  (Quantification{}, _) → EqUnknown
  (Builtin a, Builtin b)
    | a == b → EqYes
  (Builtin _, _) → EqNot
  (_, Builtin _) → EqNot
  (BuiltinsVar, BuiltinsVar) → EqYes
  (BuiltinsVar, _) → EqNot
  (_, BuiltinsVar) → EqNot
  -- TODO: Handle mixed?
  -- Shame.
  (Pi inT1 (Left (_, outT1)), Pi inT2 (Left (_, outT2))) →
    forceEq inT1 inT2 $ isEq (unLambda outT1) (unLambda outT2)
  (Pi inT1 (Right outT1), Pi inT2 (Right outT2)) →
    forceEq inT1 inT2 $ isEq outT1 outT2
  (Pi{}, _) → EqNot
  (Union _ _, _) → error "TODO isEq Union"
  (ListLit (Vector' (viewl → Just (x, xs))), ListLit (Vector' (viewl → Just (y, ys)))) →
    forceEq x y $ isEq (ListLit $ Vector' xs) (ListLit $ Vector' ys)
  (ListLit _, _) → EqNot
 where
  -- TODO: FRow???
  forceEq a b cont =
    case isEq a b of
      EqYes → cont
      x → x
  tryEq a b cont =
    case isEq a b of
      EqYes → cont
      _ → EqUnknown

builtinsVar ∷ TermT
builtinsVar = RecordLit $ fromList $ (\b → (TagLit $ identOfBuiltin b, Builtin b)) <$> builtinsList
data NormCtx
  = NormBinds !(Vector (Maybe TermT))
  | NormRewrite !TermT !TermT -- on normalized

data ListDropRes = TDFound !TermT | TDMissing | TDUnknown

-- | Produces a non-dependent union.
union ∷ TermT → TermT → TermT
union = curry \case
  (RecordLit l, RecordLit r) → RecordLit $ l <> r
  (l, r) → Union l $ Right r

unconsField ∷ TermT → Maybe ((TermT, TermT), TermT)
unconsField = \case
  Union l (Right (Union m (Right r))) → unconsField $ union l $ union m r
  Union (RecordLit (Vector' fi)) (Right r) → case viewl fi of
    Just (x, xs) → Just (x, union (RecordLit $ Vector' xs) r)
    Nothing → unconsField r
  RecordLit (Vector' fi) → case viewl fi of
    Just (x, xs) → Just (x, RecordLit $ Vector' xs)
    Nothing → Nothing
  _ → Nothing

-- | Processes application of `f` onto `a`.
postApp ∷ TermT → TermT → TermT
postApp f a = case f of
  Lam _ bod → applyLambda bod a
  App (Builtin RecordGet) name1 →
    let
      search a' = case unconsField a' of
        Nothing → recordGet name1 a'
        Just ((name2, v), rest) → case isEq name1 name2 of
          EqYes → v
          EqNot → search rest
          EqUnknown → recordGet name1 a'
     in
      search a
  App (Builtin RecordKeepFields) tags → recordSelectFields True tags a
  App (Builtin RecordDropFields) tags → recordSelectFields False tags a
  _ → App f a
 where
  -- Drop `x` from ListLit.
  listLitDrop ∷ TermT → TermT → ListDropRes
  listLitDrop x = \case
    ListLit (Vector' fi) →
      ifoldr
        ( \i n rec → case isEq x n of
            EqYes → TDFound $ ListLit $ Vector' $ deleteAt i fi
            EqNot → rec
            EqUnknown → TDUnknown
        )
        TDMissing
        fi
    _ → TDUnknown

  recordSelectFields keep tags fields0 = case tags of
    ListLit (Vector' (null → True)) → if keep then fields0 else RecordLit []
    _ →
      let
        stuck =
          let fun = if keep then RecordKeepFields else RecordDropFields
           in App (App (Builtin fun) tags) fields0
       in
        case unconsField fields0 of
          Nothing → stuck
          Just ((n, v), fields) → case listLitDrop n tags of
            TDFound tags' →
              (if keep then union (RecordLit [(n, v)]) else id) $ recordSelectFields keep tags' fields
            TDMissing →
              (if keep then id else union (RecordLit [(n, v)])) $ recordSelectFields keep tags fields
            TDUnknown → stuck

-- Rewrites & simplifies. In that order. Doesn't rewrite the simplified result.
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
    Block (BlockLet _ _ val into) → do
      val' ← go via val
      go (onLet val' via) $ unLambda into
    Block (BlockRewrite from to) → error "TODO rewrite BlockRewrite"
    Lam arg bod → Lam arg . Lambda <$> go (onNest via) (unLambda bod)
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
    Quantification q x a b → Quantification q x <$> go via a <*> (Lambda <$> go (onNest via) (unLambda b))
    Builtin x → pure $ Builtin x
    BuiltinsVar → pure builtinsVar
    Pi inT outT → do
      inT' ← go via inT
      outT' ← case outT of
        Left (n, x) → Left . (n,) . Lambda <$> go (onNest via) (unLambda x)
        Right x → Right <$> go via x
      pure $ Pi inT' outT'
    Union a b → do
      a' ← go via a
      b' ← either (\(n, b') → Left . (n,) . Lambda <$> go (onNest via) (unLambda b')) (fmap Right . go via) b
      pure $ case (a', b') of
        (RecordLit a'', Right (RecordLit b'')) → RecordLit $ a'' <> b''
        _ → Union a' b'
    ExVar n i t → ExVar n i <$> traverse (go via) t
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
      (\new old → (fmap nested <$> old) |> Just new)
      (\old → (fmap nested <$> old) |> Nothing)
      ( \term binds → case term of
          Var i →
            pure
              $ Just
              $ let after = drop (length binds - i - 1) binds
                 in case after of
                      (viewl → Just (Just val, _)) → val
                      _ → Var $ i - foldl' (\acc x → if isJust x then acc + 1 else acc) 0 after
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

normalizeBuiltin ∷ TermT → TermT
normalizeBuiltin = normalize (Just . Builtin <$> fromList builtinsList)

{- | Parse builtin
Just a variation of parseQQ that has all the builtins in scope from the start.
-}
parseBQQ ∷ QuasiQuoter
parseBQQ =
  QuasiQuoter
    { quoteExp = \s → ⟦normalizeBuiltin $(quoteExp (parseQQ $ identOfBuiltin <$> fromList builtinsList) s)⟧
    , quotePat = error "No pattern support"
    , quoteType = error "No type support"
    , quoteDec = error "No declaration support"
    }

normalizeFile ∷ FilePath → IO ()
normalizeFile x = do
  t ← parseFile x
  render $ pTerm' $ normalize [] t
