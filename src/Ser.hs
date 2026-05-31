-- | Serialization of CompileResult
module Ser where

import Compiler (CompileResult, Instr (..), TagSet, Value (..))
import Control.Monad (replicateM)
import Data.ByteString qualified as B
import Data.IntMap.Strict qualified as IM
import Data.List (sortOn)
import Data.RRBVector (Vector)
import Data.Serialize qualified as S
import GHC.Exts (IsList (..))
import Parser (Bits (..), BuiltinT (..), Ident (..), NumDesc (..), OpaqueId (..), regIdent)
import RIO hiding (Vector, toList)
import RIO.HashMap qualified as HM

-- ===========================================================================
-- CompileResult
-- ===========================================================================

serializeCompileResult :: CompileResult -> ByteString
serializeCompileResult = S.runPut . putCompileResult

deserializeCompileResult :: ByteString -> Either String CompileResult
deserializeCompileResult = S.runGet getCompileResult

putCompileResult :: CompileResult -> S.Put
putCompileResult ((tagsMap, tagSetsMap), instrs) = do
  putIdentsVec tagsMap
  putHashMap putTagSet S.putWord64le tagSetsMap
  putVector (putVector putInstr) instrs

getCompileResult :: S.Get CompileResult
getCompileResult = do
  tagsMap <- getIdentsVec
  tagSetsMap <- getHashMap getTagSet S.getWord64le
  instrs <- getVector $ getVector getInstr
  pure ((tagsMap, tagSetsMap), instrs)

-- ===========================================================================
-- Idents (dense vector, indexed by tag_id)
-- ===========================================================================

putIdentsVec :: HashMap Ident Word64 -> S.Put
putIdentsVec tagsMap = do
  let n = HM.size tagsMap
  S.putWord32le $ fromIntegral n
  let sorted = sortOn snd $ HM.toList tagsMap
  for_ sorted $ \(Ident bs isOp, _i) -> putByteStringLen bs *> putBool8 isOp

getIdentsVec :: S.Get (HashMap Ident Word64)
getIdentsVec = do
  len <- fromIntegral <$> S.getWord32le
  idents <- replicateM len $ Ident <$> getByteStringLen <*> getBool8
  pure $ HM.fromList $ zip idents (map fromIntegral [0 .. len - 1])

-- ===========================================================================
-- HashMap / TagSet / Vector helpers
-- ===========================================================================

putHashMap :: (a -> S.Put) -> (b -> S.Put) -> HashMap a b -> S.Put
putHashMap putKey putVal hm = do
  S.putWord32le $ fromIntegral $ HM.size hm
  for_ (HM.toList hm) \(k, v) -> putKey k *> putVal v

getHashMap :: (Eq a, Hashable a) => S.Get a -> S.Get b -> S.Get (HashMap a b)
getHashMap getKey getVal = do
  len <- fromIntegral <$> S.getWord32le
  pairs <- replicateM len $ (,) <$> getKey <*> getVal
  pure $ HM.fromList pairs

putTagSet :: TagSet -> S.Put
putTagSet tagSet = do
  S.putWord32le $ fromIntegral $ IM.size tagSet
  for_ (IM.toAscList tagSet) \(k, v) -> do
    S.putWord64le $ fromIntegral k
    S.putWord8 v

getTagSet :: S.Get TagSet
getTagSet = do
  len <- fromIntegral <$> S.getWord32le
  pairs <- replicateM len do
    k <- fromIntegral <$> S.getWord64le
    v <- S.getWord8
    pure (k, v)
  pure $ IM.fromList pairs

putVector :: (a -> S.Put) -> Vector a -> S.Put
putVector putItem vec = do
  S.putWord32le $ fromIntegral $ length vec
  for_ (toList vec) putItem

getVector :: S.Get a -> S.Get (Vector a)
getVector getItem = do
  len <- fromIntegral <$> S.getWord32le
  items <- replicateM len getItem
  pure $ fromList items

-- ===========================================================================
-- Instr
-- ===========================================================================

putInstr :: Instr -> S.Put
putInstr = \case
  IPush v -> S.putWord8 0 *> putValue v
  IPushVar -> S.putWord8 1
  ICopy n -> S.putWord8 2 *> S.putWord8 n
  IPopVar -> S.putWord8 3
  IApp n -> S.putWord8 4 *> S.putWord8 n
  IClosure captures args body -> do
    S.putWord8 5
    S.putWord8 captures
    S.putWord8 args
    putVector putInstr body
  IIfElse t f -> do
    S.putWord8 6
    putVector putInstr t
    putVector putInstr f
  IMkList n -> S.putWord8 7 *> S.putWord8 n
  IMkRecord n -> S.putWord8 8 *> S.putWord8 n
  IMkQRecord ts n -> S.putWord8 9 *> S.putWord64le ts *> S.putWord8 n
  IRecordCat -> S.putWord8 10

getInstr :: S.Get Instr
getInstr = do
  tag <- S.getWord8
  case tag of
    0 -> IPush <$> getValue
    1 -> pure IPushVar
    2 -> ICopy <$> S.getWord8
    3 -> pure IPopVar
    4 -> IApp <$> S.getWord8
    5 -> do
      captures <- S.getWord8
      args <- S.getWord8
      body <- getVector getInstr
      pure $ IClosure captures args body
    6 -> IIfElse <$> getVector getInstr <*> getVector getInstr
    7 -> IMkList <$> S.getWord8
    8 -> IMkRecord <$> S.getWord8
    9 -> IMkQRecord <$> S.getWord64le <*> S.getWord8
    10 -> pure IRecordCat
    _ -> fail "Unknown instruction tag"

-- ===========================================================================
-- Value
-- ===========================================================================

putValue :: Value -> S.Put
putValue = \case
  VNum x -> S.putWord8 0 *> S.putInt64le x
  VTag x -> S.putWord8 1 *> S.putWord64le x
  VBool b -> S.putWord8 2 *> putBool8 b
  VList xs -> S.putWord8 3 *> putVector putValue xs
  VRecord i xs -> S.putWord8 4 *> S.putInt64le (fromIntegral i) *> putVector putValue xs
  VBuiltinsVar -> S.putWord8 5
  VBuiltin b -> S.putWord8 6 *> putBuiltin b
  VPanic -> S.putWord8 7
  VImport x -> S.putWord8 8 *> S.putWord64le x

getValue :: S.Get Value
getValue = do
  tag <- S.getWord8
  case tag of
    0 -> VNum <$> S.getInt64le
    1 -> VTag <$> S.getWord64le
    2 -> VBool <$> getBool8
    3 -> VList <$> getVector getValue
    4 -> VRecord <$> (fromIntegral <$> S.getInt64le) <*> getVector getValue
    5 -> pure VBuiltinsVar
    6 -> VBuiltin <$> getBuiltin
    7 -> pure VPanic
    8 -> VImport <$> S.getWord64le
    _ -> fail "Unknown value tag"

-- ===========================================================================
-- BuiltinT — canonical tag scheme
-- ===========================================================================

putBuiltin :: BuiltinT -> S.Put
putBuiltin = \case
  -- Non-Kol (0–29)
  Any' -> S.putWord8 0
  Bool -> S.putWord8 1
  Eq -> S.putWord8 2
  Loop -> S.putWord8 3
  If -> S.putWord8 4
  IntEq -> S.putWord8 5
  IntGte0 -> S.putWord8 6
  List -> S.putWord8 7
  ListIndexL -> S.putWord8 8
  ListLength -> S.putWord8 9
  ListViewL -> S.putWord8 10
  Never -> S.putWord8 11
  OpaqueVal (OpaqueId _ x) -> S.putWord8 12 *> S.putWord64le (fromIntegral x)
  RecordDropFields -> S.putWord8 13
  RecordGet -> S.putWord8 14
  RecordKeepFields -> S.putWord8 15
  Refl -> S.putWord8 16
  RowPlus -> S.putWord8 17
  Tag -> S.putWord8 18
  TagEq -> S.putWord8 19
  TypePlus -> S.putWord8 20
  W -> S.putWord8 21
  WUnwrap -> S.putWord8 22
  WWrap -> S.putWord8 23
  Int' d -> S.putWord8 24 *> putNumDesc d
  IntAdd d -> S.putWord8 25 *> putNumDesc d
  IntMul d -> S.putWord8 26 *> putNumDesc d
  IntNeg d -> S.putWord8 27 *> putNumDesc d
  PropListViewlDec -> S.putWord8 28
  PropLteTrans -> S.putWord8 29
  -- Kol domain (30–49): builtinsList order
  KolDataId -> S.putWord8 30
  KolGear -> S.putWord8 31
  KolId -> S.putWord8 32
  KolLocEventId -> S.putWord8 33
  KolMkEventType -> S.putWord8 34
  KolMkGear -> S.putWord8 35
  KolQuery -> S.putWord8 36
  KolUserId -> S.putWord8 37
  KolEventTypeId -> S.putWord8 38
  KolMkStateGraph -> S.putWord8 39
  KolQueryDelta -> S.putWord8 40
  KolSenderToUser -> S.putWord8 41
  KolSgCtxDepQuery -> S.putWord8 42
  KolSgCtxQuery -> S.putWord8 43
  KolSgCtxUpdate -> S.putWord8 44
  KolStateGraphApply -> S.putWord8 45
  KolStateGraphOut -> S.putWord8 46
  KolStateGraphOutT -> S.putWord8 47
  KolStateGraphT -> S.putWord8 48
  KolTimestamp -> S.putWord8 49
  KolResolveData -> S.putWord8 50
  KolMkQuery -> S.putWord8 51
  KolResolveEvent -> S.putWord8 52
  KolUserEq -> S.putWord8 53
  KolMkAnchorAgg -> S.putWord8 54
  KolAnchorAggApply -> S.putWord8 55
  KolMkTextAgg -> S.putWord8 56
  KolTextAggApply -> S.putWord8 57
  KolTextAggMerge -> S.putWord8 58
  KolSecondaryGet -> S.putWord8 59
  KolLoopIter -> S.putWord8 60
  KolIterList -> S.putWord8 61
  KolListNew -> S.putWord8 62
  KolListPush -> S.putWord8 63
  KolSenderId -> S.putWord8 64
  KolLocalUserId -> S.putWord8 65
  KolTextUpdT -> S.putWord8 66
  KolAnchorAggT -> S.putWord8 67
  KolTextAggT -> S.putWord8 68
  _ → S.putWord8 0 -- FIX NOW

getBuiltin :: S.Get BuiltinT
getBuiltin = do
  tag <- S.getWord8
  case tag of
    -- Non-Kol (0–29)
    0 -> pure Any'
    1 -> pure Bool
    2 -> pure Eq
    3 -> pure Loop
    4 -> pure If
    5 -> pure IntEq
    6 -> pure IntGte0
    7 -> pure List
    8 -> pure ListIndexL
    9 -> pure ListLength
    10 -> pure ListViewL
    11 -> pure Never
    12 -> do
      x <- fromIntegral <$> S.getWord64le
      pure $ OpaqueVal (OpaqueId (regIdent "<deser>") x)
    13 -> pure RecordDropFields
    14 -> pure RecordGet
    15 -> pure RecordKeepFields
    16 -> pure Refl
    17 -> pure RowPlus
    18 -> pure Tag
    19 -> pure TagEq
    20 -> pure TypePlus
    21 -> pure W
    22 -> pure WUnwrap
    23 -> pure WWrap
    24 -> Int' <$> getNumDesc
    25 -> IntAdd <$> getNumDesc
    26 -> IntMul <$> getNumDesc
    27 -> IntNeg <$> getNumDesc
    28 -> pure PropListViewlDec
    29 -> pure PropLteTrans
    -- Kol domain (30–49)
    30 -> pure KolDataId
    31 -> pure KolGear
    32 -> pure KolId
    33 -> pure KolLocEventId
    34 -> pure KolMkEventType
    35 -> pure KolMkGear
    36 -> pure KolQuery
    37 -> pure KolUserId
    38 -> pure KolEventTypeId
    39 -> pure KolMkStateGraph
    40 -> pure KolQueryDelta
    41 -> pure KolSenderToUser
    42 -> pure KolSgCtxDepQuery
    43 -> pure KolSgCtxQuery
    44 -> pure KolSgCtxUpdate
    45 -> pure KolStateGraphApply
    46 -> pure KolStateGraphOut
    47 -> pure KolStateGraphOutT
    48 -> pure KolStateGraphT
    49 -> pure KolTimestamp
    50 -> pure KolResolveData
    51 -> pure KolMkQuery
    52 -> pure KolResolveEvent
    53 -> pure KolUserEq
    54 -> pure KolMkAnchorAgg
    55 -> pure KolAnchorAggApply
    56 -> pure KolMkTextAgg
    57 -> pure KolTextAggApply
    58 -> pure KolTextAggMerge
    59 -> pure KolSecondaryGet
    60 -> pure KolLoopIter
    61 -> pure KolIterList
    62 -> pure KolListNew
    63 -> pure KolListPush
    64 -> pure KolSenderId
    65 -> pure KolLocalUserId
    66 -> pure KolTextUpdT
    67 -> pure KolAnchorAggT
    68 -> pure KolTextAggT
    _ -> fail "Unknown builtin tag"

-- ===========================================================================
-- NumDesc / Bits
-- ===========================================================================

putNumDesc :: NumDesc -> S.Put
putNumDesc = \case
  NumFin nonNeg bits -> do
    S.putWord8 0
    putBool8 nonNeg
    putBits bits
  NumInf -> S.putWord8 1

getNumDesc :: S.Get NumDesc
getNumDesc =
  S.getWord8 >>= \case
    0 -> NumFin <$> getBool8 <*> getBits
    1 -> pure NumInf
    _ -> fail "Unknown num desc"

putBits :: Bits -> S.Put
putBits =
  S.putWord8 . \case
    Bits8 -> 0
    Bits16 -> 1
    Bits32 -> 2
    Bits64 -> 3

getBits :: S.Get Bits
getBits = do
  tag <- S.getWord8
  case tag of
    0 -> pure Bits8
    1 -> pure Bits16
    2 -> pure Bits32
    3 -> pure Bits64
    _ -> fail "Unknown bits tag"

-- ===========================================================================
-- Ident / primitives
-- ===========================================================================

putIdent :: Ident -> S.Put
putIdent (Ident bs isOp) = putByteStringLen bs *> putBool8 isOp

getIdent :: S.Get Ident
getIdent = Ident <$> getByteStringLen <*> getBool8

putByteStringLen :: ByteString -> S.Put
putByteStringLen bs = S.putWord32le (fromIntegral $ B.length bs) *> S.putByteString bs

getByteStringLen :: S.Get ByteString
getByteStringLen = do
  len <- fromIntegral <$> S.getWord32le
  S.getByteString len

putBool8 :: Bool -> S.Put
putBool8 b = S.putWord8 $ if b then 1 else 0

getBool8 :: S.Get Bool
getBool8 = do
  b <- S.getWord8
  case b of
    0 -> pure False
    1 -> pure True
    _ -> fail "Invalid boolean value"
