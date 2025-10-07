-- This is absolutely horrfying and has strict limits which aren't even checked properly
module Compiler where

import Control.Algebra
import Control.Carrier.Empty.Church (runEmpty)
import Control.Carrier.Reader (ask, local, runReader)
import Control.Carrier.State.Church (State, StateC, evalState, execState, get, put, runState)
import Control.Carrier.Writer.Church (WriterC, execWriter, tell)
import Control.Effect.Empty (Empty, empty)
import Control.Effect.State (modify, state)
import Control.Monad (replicateM)
import Data.Foldable (foldl)
import Data.Foldable qualified as Foldable
import Data.IntMap.Strict qualified as IM
import Data.IntSet qualified as IS
import Data.List qualified as List
import Data.RRBVector (Vector, drop, ifoldl, ifoldl', imap, replicate, reverse, splitAt, take, viewl, viewr, zip, (!?), (<|), (|>))
import Data.Serialize qualified as S
import GHC.Exts (IsList (..))
import Normalize (splitAt3)
import Parser (Bits (..), BlockF (..), BuiltinT (..), Fields (..), Ident (..), Lambda (..), NumDesc (..), Quant (..), Term (..), TermF (..), Vector' (..), nestedByP, traverseTermF)
import RIO hiding (Vector, ask, drop, local, replicate, reverse, runReader, take, toList, zip)
import RIO.ByteString qualified as B
import RIO.HashMap qualified as HM

-- Unfortunately, not a rewrite', since this just erases & is not meant to
-- simplify anything
erase ∷ Vector Bool → Term → Term
erase reals =
  unTerm >>> \case
    Lam QEra _ body → erase (reals |> False) $ unLambda body
    AppErased f _ → erase reals f
    Block (BlockRewrite _ into) → erase reals into
    Var x → Term $ Var $ x - foldl' (\erased isReal → if isReal then erased else erased + 1) 0 (drop (length reals - x) reals)
    x → Term $ run $ traverseTermF (Identity . erase reals) (Identity . Lambda . erase (reals |> True) . unLambda) x

listCaptures ∷ Word8 → Lambda Term → IntSet
listCaptures locals0 = run . execWriter . runReader @Int (fromIntegral locals0) . go . unLambda
 where
  go = fix \rec →
    unTerm >>> \case
      Var x → do
        locals ← ask @Int
        when (x >= locals) $ tell @IntSet [x - locals]
      x → void $ traverseTermF rec (local @Int (+ 1) . fmap Lambda . rec . unLambda) x

-- A helper function that identifies trivially nested lambdas `\x y z. ...`
-- Proper type: Fun (Lambda 1 Term) -> (self : { .n : Int } \/ { .lam : Lambda self.n Term })
getLambdaN ∷ Lambda Term → (Word8, Lambda Term)
getLambdaN lam = case unLambda lam of
  Term (Lam QNorm _ body) → first (+ 1) $ getLambdaN body
  body → (1, Lambda body)

lambdaToClosure ∷ Word8 → Lambda Term → (IntSet, Lambda Term)
lambdaToClosure n orig =
  let
    captures = listCaptures n orig
    realCaptures = reverse $ imap (\i () → i `IS.member` captures) (replicate (maybe 0 fst $ IS.maxView captures) ())
   in
    (captures, Lambda $ erase (realCaptures <> replicate (fromIntegral n) True) $ unLambda orig)

getAppN ∷ (Term, Vector Term) → (Term, Vector Term)
getAppN (Term (App f a), args) = getAppN (f, a <| args)
getAppN (f, args) = (f, args)

data Value
  = VNum !Int64
  | VTag !Word64
  | VBool !Bool
  | VList !(Vector Value)
  | VRecord !Word64 !(Vector Value)
  | -- | VLam !(Vector Value) !(Vector Instr) -- exists, but current compiler never emits it
    VBuiltinsVar
  | VBuiltin !BuiltinT
  | VPanic
  deriving
    ( -- | Pi !Quant !Term !(Either (Ident, Lambda Term) Term)
      -- | Concat !Term !(Either (Ident, Lambda Term) Term)
      Show
    , Eq
    )

{-
Basically, all the instruction set is just a "flat" sequence of operations that builds a tree.
All intermediate values are pushed on the stack.
It also has bindings (registers) that it can refer to.

NOTE: currently we don't mess with numbers. IApp 0 = applying 0 arguments.
-}
data Instr
  = IPush !Value
  | IPushVar
  | ICopy !Word8
  | IPopVar -- pop value BEFORE last one. `[a, b, c, d]` -> `[IPopVar]` -> `[a, b, d]`
  | IApp !Word8 -- apply n arguments
  | IClosure !Word8 !Word8 !(Vector Instr)
  | IIfElse !(Vector Instr) !(Vector Instr)
  | IMkList !Word8
  | IMkRecord !Word8 -- consumes n values and n keys
  | IMkQRecord !Word64 !Word8 -- [archetype] [n] -- consumes n values
  deriving (Show, Eq)

type RawTag = Ident
type TagSet = IntMap Word8

type CodeGen = StateC (Vector Bool) (WriterC (Vector Instr) Identity) () -- True where slot represents a variable
data Module = MEmpty | MConst !Value | MGen !CodeGen

-- | Track a new push to the stack, without actually emitting instructions.
trackPush ∷ Bool → CodeGen
trackPush isVar = modify @(Vector Bool) (|> isVar)

-- | Reverse trackPush
trackPop ∷ Word8 → CodeGen
trackPop x = modify @(Vector Bool) \l → take (length l - fromIntegral x) l

-- | Emit instruction & track stack updates
instr ∷ Instr → CodeGen
instr x = do
  case x of
    IPush _ → trackPush False
    IPushVar → trackPop 1 *> trackPush True
    ICopy _ → trackPush False
    IPopVar → trackPop 2 *> trackPush False
    IApp args → trackPop (args + 1) *> trackPush False
    IClosure captures _args _body → trackPop captures *> trackPush False
    IIfElse _ _ → trackPop 1 *> trackPush False
    IMkList n → trackPop n *> trackPush False
    IMkRecord n → trackPop (2 * n) *> trackPush False
    IMkQRecord _ n → trackPop n *> trackPush False
  tell @(Vector Instr) [x]

toCodeGen ∷ Module → CodeGen
toCodeGen = \case
  MConst x → instr $ IPush x
  MGen gen → gen
  MEmpty → pure ()
instance Semigroup Module where
  MEmpty <> b = b
  a <> MEmpty = a
  (toCodeGen → genA) <> (toCodeGen → genB) = MGen $ genA *> genB
instance Monoid Module where
  mempty = MEmpty

execCodeGen ∷ Vector Bool → CodeGen → Vector Instr
execCodeGen ctx act = run $ execWriter $ evalState ctx act

type Compile = State (HashMap Ident Word64) :+: State (HashMap TagSet Word64)

icopy ∷ Int → CodeGen
icopy varDepth0 = do
  vars ← get @(Vector Bool)
  let
    slotI' =
      ifoldl
        ( \slotI rec isVar varDepth →
            if isVar
              then if varDepth == 0 then slotI else rec (varDepth - 1)
              else rec varDepth
        )
        (\_ → error "Variable not found")
        vars
        varDepth0
  instr $ ICopy $ fromIntegral $ length vars - slotI' - 1

registry ∷ ∀ r sig m. (Has (State (HashMap r Word64)) sig m, Hashable r) ⇒ r → m Word64
registry val = do
  toI ← get @(HashMap r Word64)
  case HM.lookup val toI of
    Just i → pure i
    Nothing → do
      let i = fromIntegral $ HM.size toI
      put $ HM.insert val i toI
      pure i

mkTagSet ∷ (Has Compile sig m) ⇒ Vector (Word64, a) → m (Word64, Vector a)
mkTagSet keyvalues = do
  let organized = foldl' (\acc (k, v) → IM.alter (Just . (|> v) . fromMaybe []) (fromIntegral k) acc) IM.empty keyvalues
  (,snd =<< fromList (IM.toAscList organized)) <$> registry (fromIntegral @_ @Word8 . length <$> organized)

toConstM ∷ Module → Maybe Value
toConstM = \case
  MConst x → Just x
  _ → Nothing

toTagM ∷ Value → Maybe Word64
toTagM = \case
  VTag x → Just x
  _ → Nothing

-- compiles erased
compile' ∷ (Has Compile sig m) ⇒ Term → m Module
compile' =
  unTerm >>> \case
    NumLit x → pure $ MConst $ VNum $ fromIntegral x
    TagLit tag → MConst . VTag <$> registry tag
    BoolLit x → pure $ MConst $ VBool x
    ListLit (Vector' entries) → do
      values0 ← for entries compile'
      pure case traverse toConstM values0 of
        Nothing → fold values0 <> MGen (instr $ IMkList $ fromIntegral $ length entries)
        Just values → MConst $ VList values
    FieldsLit (FRecord ()) (Vector' entries) → do
      kv0 ← for entries \(k, v) → (,) <$> compile' k <*> compile' v
      let n = fromIntegral $ length entries
      (values, mkRecord) ← case traverse (\(k, v) → (,v) <$> (toConstM k >>= toTagM)) kv0 of
        Nothing → pure (snd <$> kv0, foldMap fst kv0 <> MGen (instr $ IMkRecord $ fromIntegral $ length entries))
        Just kv → do
          (ts, values) ← mkTagSet kv
          pure (values, MGen $ instr $ IMkQRecord ts n)
      pure $ fold values <> mkRecord -- ts <> MGen (instr $ IMkRecord $ fromIntegral $ length entries)
    FieldsLit (FRow ()) _ → error "TODO"
    BuiltinsVar → pure $ MConst VBuiltinsVar
    Builtin x → pure $ MConst $ VBuiltin x
    Lam QNorm _ body → do
      let
        (n, body') = getLambdaN body
        (captures, body'') = lambdaToClosure n body'
      bodyModule ← compile' $ unLambda body''
      let
        captures' = MGen . icopy <$> IS.toAscList captures
        closureVars = replicate (fromIntegral n + IS.size captures) True
        closure =
          MGen
            $ instr
            $ IClosure
              (fromIntegral $ IS.size captures)
              n
            $ execCodeGen closureVars
            $ toCodeGen bodyModule
      pure $ fold captures' <> closure
    Lam QEra _ _ → error "erased"
    ((unTerm → (unTerm → Term (Builtin If) `App` b) `App` t) `App` f) →
      compile' b >>= \case
        MConst (VBool b') → compile' if b' then t else f
        b' → do
          t' ← compile' t
          f' ← compile' f
          pure $ MGen do
            ctx ← get
            toCodeGen b'
            instr $ IIfElse (execCodeGen ctx $ toCodeGen t') (execCodeGen ctx $ toCodeGen f')
    App f a → do
      let (f', args) = getAppN (f, [a])
      args' ← for args compile'
      f'' ← compile' f'
      pure $ fold args' <> f'' <> MGen (instr $ IApp $ fromIntegral $ length args)
    AppErased{} → undefined
    Var x → pure $ MGen $ icopy x
    Block (BlockLet QNorm _n _ty val body) → do
      val' ← compile' val
      body' ← compile' $ unLambda body
      pure $ val' <> MGen (instr $ IPushVar) <> body' <> MGen (instr IPopVar)
    Block (BlockLet QEra _ _ _ _) → error "erased"
    Block (BlockRewrite _ _) → error "erased"
    Sorry → pure $ MConst VPanic
    Pi{} → error "TODO"
    Concat{} → error "TODO"
    ExVar{} → error "erased"
    UniVar{} → error "erased"

type CompileResult = ((HashMap Ident Word64, HashMap TagSet Word64), Vector Instr)

compile ∷ Term → CompileResult
compile term =
  let (tags, (tagSets, m)) = run $ runState @(HashMap Ident Word64) (curry pure) mempty $ runState @(HashMap TagSet Word64) (curry pure) mempty $ compile' term
   in ((tags, tagSets), execCodeGen [] $ toCodeGen m)

decompile ∷ CompileResult → Maybe Term
decompile ((tags0, tagSets0), instrs00) =
  run
    $ runEmpty (pure Nothing) (pure . Just)
    $ evalState @(Vector Instr) instrs00
    $ evalState @(Vector (Maybe Term)) [] scope
 where
  tags = IM.fromList $ (\(a, b) → (fromIntegral b, a)) <$> toList tags0
  tagSets = IM.fromList $ (\(a, b) → (fromIntegral b, a)) <$> toList tagSets0
  popInstr = do
    iis ← viewl <$> get @(Vector Instr)
    put (maybe [] snd iis)
    pure $ fst <$> iis
  pushStack x = modify (|> x)
  popStackVal = do
    (vs, vM) ← maybe empty pure =<< viewr <$> get @(Vector (Maybe Term))
    v ← maybe empty pure vM
    put vs $> v
  popStackValLastN n = do
    -- (state: [a, b, c, d]) |- 2 --> [c, d]
    res ← state \s → splitAt (length s - fromIntegral n) s
    unless (length res == fromIntegral n) empty
    for res $ maybe empty pure
  decompileTag t = maybe empty (pure . Term . TagLit) $ IM.lookup (fromIntegral t) tags
  mkRecord tIdx values = do
    tagSet ← maybe empty pure (IM.lookup (fromIntegral tIdx) tagSets)
    let keys = fromList (IM.toAscList tagSet) >>= \(k, vs) → replicate (fromIntegral vs) k
    Term . FieldsLit (FRecord ()) . Vector' <$> for (zip keys values) \(k, v) →
      (,v) <$> decompileTag (fromIntegral k)
  decompileValue = \case
    VNum n → pure $ Term $ NumLit $ fromIntegral n
    VBool b → pure $ Term $ BoolLit b
    VList vs → Term . ListLit . Vector' <$> traverse decompileValue vs
    VBuiltinsVar → pure $ Term BuiltinsVar
    VBuiltin b → pure $ Term $ Builtin b
    VPanic → pure $ Term Sorry
    VTag t → decompileTag t
    VRecord tIdx values → mkRecord tIdx =<< traverse decompileValue values
  subdecompile (stack ∷ Vector (Maybe Term)) instrs = do
    (stack0 ∷ Vector (Maybe Term), instrs0 ∷ Vector Instr) ← (,) <$> get <*> get
    put stack *> put instrs
    scope <* put stack0 <* put instrs0
  scope =
    popInstr >>= \case
      Nothing → popStackVal
      Just currInstr → case currInstr of
        IPopVar → popStackVal -- no continue
        IPush v → do
          t ← decompileValue v
          pushStack $ Just t
          scope
        IPushVar → do
          val ← popStackVal
          res ←
            Term . Block . BlockLet QNorm Nothing Nothing val . Lambda <$> do
              ctx0 ← get @(Vector (Maybe Term))
              put $ ctx0 |> Nothing
              scope <* put ctx0
          pushStack $ Just res
          scope
        ICopy i → do
          stack ← get @(Vector (Maybe Term))
          case splitAt3 (length stack - fromIntegral i - 1) stack of
            (_, Just t, after) → do
              traceShowM t
              traceShowM after
              let res = Just $ fromMaybe (Term $ Var 0) t `nestedByP` foldl' (\acc x → if isNothing x then acc + 1 else acc) 0 after
              traceShowM res
              traceShowM "---"
              pushStack res
            _ → empty
          scope
        IApp argsN → do
          f ← popStackVal
          args ← popStackValLastN argsN
          let res = foldl' (\f' a' → Term $ f' `App` a') f args
          pushStack $ Just res
          scope
        IClosure capturesN argsN lamInstrs → do
          captures ← popStackValLastN capturesN
          res ←
            flip (foldl' @[] \t _c → Term $ Lam QNorm Nothing $ Lambda t) [1 .. argsN]
              <$> let lamStack = fmap Just captures <> replicate (fromIntegral argsN) Nothing
                   in subdecompile lamStack lamInstrs
          pushStack $ Just res
          scope
        IIfElse tInstr fInstr → do
          cond ← popStackVal
          stack ← get
          t ← subdecompile stack tInstr
          f ← subdecompile stack fInstr
          pushStack $ Just $ Term $ Term (Term (Term (Builtin If) `App` cond) `App` t) `App` f
          scope
        IMkList n → do
          l ← popStackValLastN n
          pushStack $ Just $ Term $ ListLit $ Vector' l
          scope
        IMkRecord n → do
          keys ← popStackValLastN n
          values ← popStackValLastN n
          pushStack $ Just $ Term $ FieldsLit (FRecord ()) $ Vector' $ zip keys values
          scope
        IMkQRecord ts n → do
          values ← popStackValLastN n
          pushStack . Just =<< mkRecord ts values
          scope

-- modify @(Vector Term) (\s → s |> (fromMaybe (error "impossible") $ s ?! _)) *> scope
-- run = d

-- serializeCompileResult ∷ CompileResult → ByteString
-- serializeCompileResult = S.runPut . putCompileResult

-- deserializeCompileResult ∷ ByteString → Either String CompileResult
-- deserializeCompileResult = S.runGet getCompileResult

-- putCompileResult ∷ CompileResult → S.Put
-- putCompileResult ((tagsMap, tagSetsMap), instrs) = do
--   putHashMap putIdent S.putWord64le tagsMap
--   putHashMap putTagSet S.putWord64le tagSetsMap
--   putVector putInstr instrs

-- getCompileResult ∷ S.Get CompileResult
-- getCompileResult = do
--   tagsMap ← getHashMap getIdent S.getWord64le
--   tagSetsMap ← getHashMap getTagSet S.getWord64le
--   instrs ← getVector getInstr
--   pure ((tagsMap, tagSetsMap), instrs)

-- putHashMap ∷ (a → S.Put) → (b → S.Put) → HashMap a b → S.Put
-- putHashMap putKey putVal hm = do
--   S.putWord32le $ fromIntegral $ HM.size hm
--   for_ (HM.toList hm) \(k, v) → putKey k *> putVal v

-- getHashMap ∷ (Eq a, Hashable a) ⇒ S.Get a → S.Get b → S.Get (HashMap a b)
-- getHashMap getKey getVal = do
--   len ← fromIntegral <$> S.getWord32le
--   pairs ← replicateM len $ (,) <$> getKey <*> getVal
--   pure $ HM.fromList pairs

-- putTagSet ∷ TagSet → S.Put
-- putTagSet tagSet = do
--   S.putWord32le $ fromIntegral $ IM.size tagSet
--   for_ (IM.toAscList tagSet) \(k, v) → do
--     S.putWord64le $ fromIntegral k
--     S.putWord8 v

-- getTagSet ∷ S.Get TagSet
-- getTagSet = do
--   len ← fromIntegral <$> S.getWord32le
--   pairs ← replicateM len do
--     k ← fromIntegral <$> S.getWord64le
--     v ← S.getWord8
--     pure (k, v)
--   pure $ IM.fromList pairs

-- putVector ∷ (a → S.Put) → Vector a → S.Put
-- putVector putItem vec = do
--   S.putWord32le $ fromIntegral $ length vec
--   for_ (Foldable.toList vec) putItem

-- getVector ∷ S.Get a → S.Get (Vector a)
-- getVector getItem = do
--   len ← fromIntegral <$> S.getWord32le
--   items ← replicateM len getItem
--   pure $ fromList items

-- putInstr ∷ Instr → S.Put
-- putInstr = \case
--   IPush v → S.putWord8 0 *> putValue v
--   IPushVar → S.putWord8 1
--   ICopy n → S.putWord8 2 *> S.putWord8 n
--   IPopVar → S.putWord8 3
--   IApp n → S.putWord8 4 *> S.putWord8 n
--   IClosure captures args body → do
--     S.putWord8 5
--     S.putWord8 captures
--     S.putWord8 args
--     putVector putInstr body
--   IIfElse t f → do
--     S.putWord8 6
--     putVector putInstr t
--     putVector putInstr f
--   IMkList n → S.putWord8 7 *> S.putWord8 n
--   IMkRecord n → S.putWord8 8 *> S.putWord8 n
--   IMkQRecord ts n → S.putWord8 9 *> S.putWord64le ts *> S.putWord8 n

-- getInstr ∷ S.Get Instr
-- getInstr = do
--   tag ← S.getWord8
--   case tag of
--     0 → IPush <$> getValue
--     1 → pure IPushVar
--     2 → ICopy <$> S.getWord8
--     3 → pure IPopVar
--     4 → IApp <$> S.getWord8
--     5 → do
--       captures ← S.getWord8
--       args ← S.getWord8
--       body ← getVector getInstr
--       pure $ IClosure captures args body
--     6 → IIfElse <$> getVector getInstr <*> getVector getInstr
--     7 → IMkList <$> S.getWord8
--     8 → IMkRecord <$> S.getWord8
--     9 → IMkQRecord <$> S.getWord64le <*> S.getWord8
--     _ → fail "Unknown instruction tag"

-- putValue ∷ Value → S.Put
-- putValue = \case
--   VNum x → S.putWord8 0 *> S.putInt64le x
--   VTag x → S.putWord8 1 *> S.putWord64le x
--   VBool b → S.putWord8 2 *> putBool8 b
--   VList xs → S.putWord8 3 *> putVector putValue xs
--   VRecord i xs → S.putWord8 4 *> S.putInt64le (fromIntegral i) *> putVector putValue xs
--   VBuiltinsVar → S.putWord8 5
--   VBuiltin b → S.putWord8 6 *> putBuiltin b
--   VPanic → S.putWord8 7

-- getValue ∷ S.Get Value
-- getValue = do
--   tag ← S.getWord8
--   case tag of
--     0 → VNum <$> S.getInt64le
--     1 → VTag <$> S.getWord64le
--     2 → VBool <$> getBool8
--     3 → VList <$> getVector getValue
--     4 → VRecord <$> (fromIntegral <$> S.getInt64le) <*> getVector getValue
--     5 → pure VBuiltinsVar
--     6 → VBuiltin <$> getBuiltin
--     7 → pure VPanic
--     _ → fail "Unknown value tag"

-- putBuiltin ∷ BuiltinT → S.Put
-- putBuiltin = \case
--   Tag → S.putWord8 0
--   RowPlus → S.putWord8 1
--   List → S.putWord8 2
--   Bool → S.putWord8 3
--   TypePlus → S.putWord8 4
--   Eq → S.putWord8 5
--   Refl → S.putWord8 6
--   RecordGet → S.putWord8 7
--   RecordKeepFields → S.putWord8 8
--   RecordDropFields → S.putWord8 9
--   ListLength → S.putWord8 10
--   ListIndexL → S.putWord8 11
--   NatFold → S.putWord8 12
--   If → S.putWord8 13
--   IntGte0 → S.putWord8 14
--   IntEq → S.putWord8 15
--   TagEq → S.putWord8 16
--   W → S.putWord8 17
--   Wrap → S.putWord8 18
--   Unwrap → S.putWord8 19
--   Never → S.putWord8 20
--   Any' → S.putWord8 21
--   Add d → S.putWord8 22 *> putNumDesc d
--   Mul d → S.putWord8 23 *> putNumDesc d
--   Num d → S.putWord8 24 *> putNumDesc d
--   IntNeg d → S.putWord8 25 *> putNumDesc d

-- getBuiltin ∷ S.Get BuiltinT
-- getBuiltin = do
--   tag ← S.getWord8
--   case tag of
--     0 → pure Tag
--     1 → pure RowPlus
--     2 → pure List
--     3 → pure Bool
--     4 → pure TypePlus
--     5 → pure Eq
--     6 → pure Refl
--     7 → pure RecordGet
--     8 → pure RecordKeepFields
--     9 → pure RecordDropFields
--     10 → pure ListLength
--     11 → pure ListIndexL
--     12 → pure NatFold
--     13 → pure If
--     14 → pure IntGte0
--     15 → pure IntEq
--     16 → pure TagEq
--     17 → pure W
--     18 → pure Wrap
--     19 → pure Unwrap
--     20 → pure Never
--     21 → pure Any'
--     22 → Add <$> getNumDesc
--     23 → Mul <$> getNumDesc
--     24 → Num <$> getNumDesc
--     25 → IntNeg <$> getNumDesc
--     _ → fail "Unknown builtin tag"

-- putNumDesc ∷ NumDesc → S.Put
-- putNumDesc (NumDesc nonNeg bits) = do
--   putBool8 nonNeg
--   putBits bits

-- getNumDesc ∷ S.Get NumDesc
-- getNumDesc = NumDesc <$> getBool8 <*> getBits

-- putBits ∷ Bits → S.Put
-- putBits = S.putWord8 . \case
--   Bits8 → 0
--   Bits16 → 1
--   Bits32 → 2
--   Bits64 → 3
--   BitsInf → 4

-- getBits ∷ S.Get Bits
-- getBits = do
--   tag ← S.getWord8
--   case tag of
--     0 → pure Bits8
--     1 → pure Bits16
--     2 → pure Bits32
--     3 → pure Bits64
--     4 → pure BitsInf
--     _ → fail "Unknown bits tag"

-- putIdent ∷ Ident → S.Put
-- putIdent (Ident bs isOp) = putByteStringLen bs *> putBool8 isOp

-- getIdent ∷ S.Get Ident
-- getIdent = Ident <$> getByteStringLen <*> getBool8

-- putByteStringLen ∷ ByteString → S.Put
-- putByteStringLen bs = S.putWord32le (fromIntegral $ B.length bs) *> S.putByteString bs

-- getByteStringLen ∷ S.Get ByteString
-- getByteStringLen = do
--   len ← fromIntegral <$> S.getWord32le
--   S.getByteString len

-- putBool8 ∷ Bool → S.Put
-- putBool8 b = S.putWord8 $ if b then 1 else 0

-- getBool8 ∷ S.Get Bool
-- getBool8 = do
--   b ← S.getWord8
--   case b of
--     0 → pure False
--     1 → pure True
--     _ → fail "Invalid boolean value"

-- putInstr ∷ S.Putter Instr
-- putInstr = \case
--   IPush v → S.putWord8 0 *> putValue v
--   IPushVar → S.putWord8 1
--   IPopVar n → S.putWord8 2 *> S.putWord8 (fromIntegral n)
--   ICopyVar n → S.putWord8 3 *> S.putWord8 (fromIntegral n)
--   IApp n → S.putWord8 4 *> S.putWord8 (fromIntegral n)
--   IClosure a c o →
--     S.putWord8 5
--       *> S.putWord8 (fromIntegral a)
--       *> S.putWord8 (fromIntegral $ length c)
--       *> S.putListOf (S.putWord8 . fromIntegral) c
--       *> S.putWord32le (fromIntegral o)
--   IIf n → S.putWord8 6 *> S.putWord32le (fromIntegral n)
--   IElse n → S.putWord8 7 *> S.putWord32le (fromIntegral n)
--   IMkList n → S.putWord8 8 *> S.putWord32le (fromIntegral n)
--   IMkRecord n → S.putWord8 9 *> S.putWord32le (fromIntegral n)

-- compileFile ∷ FilePath → IO ()
-- compileFile file = do
--   parsed ← parseFile file
--   let (tags, unmerged) = runIdentity $ runState @(HashMap Ident Int) (curry pure) mempty $ execWriter @(Vector Instr) $ compile' parsed
--   let (profiles, merged) = merge unmerged
--   writeFileBinary (fromMaybe file (stripSuffix ".fad" file) <> ".fadobj") $ S.runPut do
--     S.putListOf (\(Ident n op) → putB n *> S.put op) $ registryToList tags
--     S.putListOf putTagProfile $ registryToList profiles
--     S.putListOf putInstr $ toList merged
