-- | Serialization of CompileResult
module Ser where

import Compiler (CompileResult, Instr (..), TagSet, Value (..))
import Control.Monad (replicateM)
import Data.ByteString qualified as B
import Data.IntMap.Strict qualified as IM
import Data.RRBVector (Vector)
import Data.Serialize qualified as S
import GHC.Exts (IsList (..))
import Parser (Bits (..), BuiltinT (..), Ident (..), NumDesc (..))
import RIO hiding (Vector, toList)
import RIO.HashMap qualified as HM

serializeCompileResult ∷ CompileResult → ByteString
serializeCompileResult = S.runPut . putCompileResult

deserializeCompileResult ∷ ByteString → Either String CompileResult
deserializeCompileResult = S.runGet getCompileResult

putCompileResult ∷ CompileResult → S.Put
putCompileResult ((tagsMap, tagSetsMap), instrs) = do
  putHashMap putIdent S.putWord64le tagsMap
  putHashMap putTagSet S.putWord64le tagSetsMap
  putVector (putVector putInstr) instrs

getCompileResult ∷ S.Get CompileResult
getCompileResult = do
  tagsMap ← getHashMap getIdent S.getWord64le
  tagSetsMap ← getHashMap getTagSet S.getWord64le
  instrs ← getVector $ getVector getInstr
  pure ((tagsMap, tagSetsMap), instrs)

putHashMap ∷ (a → S.Put) → (b → S.Put) → HashMap a b → S.Put
putHashMap putKey putVal hm = do
  S.putWord32le $ fromIntegral $ HM.size hm
  for_ (HM.toList hm) \(k, v) → putKey k *> putVal v

getHashMap ∷ (Eq a, Hashable a) ⇒ S.Get a → S.Get b → S.Get (HashMap a b)
getHashMap getKey getVal = do
  len ← fromIntegral <$> S.getWord32le
  pairs ← replicateM len $ (,) <$> getKey <*> getVal
  pure $ HM.fromList pairs

putTagSet ∷ TagSet → S.Put
putTagSet tagSet = do
  S.putWord32le $ fromIntegral $ IM.size tagSet
  for_ (IM.toAscList tagSet) \(k, v) → do
    S.putWord64le $ fromIntegral k
    S.putWord8 v

getTagSet ∷ S.Get TagSet
getTagSet = do
  len ← fromIntegral <$> S.getWord32le
  pairs ← replicateM len do
    k ← fromIntegral <$> S.getWord64le
    v ← S.getWord8
    pure (k, v)
  pure $ IM.fromList pairs

putVector ∷ (a → S.Put) → Vector a → S.Put
putVector putItem vec = do
  S.putWord32le $ fromIntegral $ length vec
  for_ (toList vec) putItem

getVector ∷ S.Get a → S.Get (Vector a)
getVector getItem = do
  len ← fromIntegral <$> S.getWord32le
  items ← replicateM len getItem
  pure $ fromList items

putInstr ∷ Instr → S.Put
putInstr = \case
  IPush v → S.putWord8 0 *> putValue v
  IPushVar → S.putWord8 1
  ICopy n → S.putWord8 2 *> S.putWord8 n
  IPopVar → S.putWord8 3
  IApp n → S.putWord8 4 *> S.putWord8 n
  IClosure captures args body → do
    S.putWord8 5
    S.putWord8 captures
    S.putWord8 args
    putVector putInstr body
  IIfElse t f → do
    S.putWord8 6
    putVector putInstr t
    putVector putInstr f
  IMkList n → S.putWord8 7 *> S.putWord8 n
  IMkRecord n → S.putWord8 8 *> S.putWord8 n
  IMkQRecord ts n → S.putWord8 9 *> S.putWord64le ts *> S.putWord8 n

getInstr ∷ S.Get Instr
getInstr = do
  tag ← S.getWord8
  case tag of
    0 → IPush <$> getValue
    1 → pure IPushVar
    2 → ICopy <$> S.getWord8
    3 → pure IPopVar
    4 → IApp <$> S.getWord8
    5 → do
      captures ← S.getWord8
      args ← S.getWord8
      body ← getVector getInstr
      pure $ IClosure captures args body
    6 → IIfElse <$> getVector getInstr <*> getVector getInstr
    7 → IMkList <$> S.getWord8
    8 → IMkRecord <$> S.getWord8
    9 → IMkQRecord <$> S.getWord64le <*> S.getWord8
    _ → fail "Unknown instruction tag"

putValue ∷ Value → S.Put
putValue = \case
  VNum x → S.putWord8 0 *> S.putInt64le x
  VTag x → S.putWord8 1 *> S.putWord64le x
  VBool b → S.putWord8 2 *> putBool8 b
  VList xs → S.putWord8 3 *> putVector putValue xs
  VRecord i xs → S.putWord8 4 *> S.putInt64le (fromIntegral i) *> putVector putValue xs
  VBuiltinsVar → S.putWord8 5
  VBuiltin b → S.putWord8 6 *> putBuiltin b
  VPanic → S.putWord8 7
  VImport x → S.putWord8 8 *> S.putInt64le x

getValue ∷ S.Get Value
getValue = do
  tag ← S.getWord8
  case tag of
    0 → VNum <$> S.getInt64le
    1 → VTag <$> S.getWord64le
    2 → VBool <$> getBool8
    3 → VList <$> getVector getValue
    4 → VRecord <$> (fromIntegral <$> S.getInt64le) <*> getVector getValue
    5 → pure VBuiltinsVar
    6 → VBuiltin <$> getBuiltin
    7 → pure VPanic
    _ → fail "Unknown value tag"

putBuiltin ∷ BuiltinT → S.Put
putBuiltin = \case
  Any' → S.putWord8 0
  Bool → S.putWord8 1
  Eq → S.putWord8 2
  Fix' → S.putWord8 3
  If → S.putWord8 4
  IntEq → S.putWord8 5
  IntGte0 → S.putWord8 6
  List → S.putWord8 7
  ListIndexL → S.putWord8 8
  ListLength → S.putWord8 9
  ListViewL → S.putWord8 10
  Never → S.putWord8 11
  RecordDropFields → S.putWord8 12
  RecordGet → S.putWord8 13
  RecordKeepFields → S.putWord8 14
  Refl → S.putWord8 15
  RowPlus → S.putWord8 16
  Tag → S.putWord8 17
  TagEq → S.putWord8 18
  TypePlus → S.putWord8 19
  W → S.putWord8 20
  WUnwrap → S.putWord8 21
  WWrap → S.putWord8 22
  Int' d → S.putWord8 23 *> putNumDesc d
  IntAdd d → S.putWord8 24 *> putNumDesc d
  IntMul d → S.putWord8 25 *> putNumDesc d
  IntNeg d → S.putWord8 26 *> putNumDesc d

getBuiltin ∷ S.Get BuiltinT
getBuiltin = do
  tag ← S.getWord8
  case tag of
    0 → pure Any'
    1 → pure Bool
    2 → pure Eq
    3 → pure Fix'
    4 → pure If
    5 → pure IntEq
    6 → pure IntGte0
    7 → pure List
    8 → pure ListIndexL
    9 → pure ListLength
    10 → pure ListViewL
    11 → pure Never
    12 → pure RecordDropFields
    13 → pure RecordGet
    14 → pure RecordKeepFields
    15 → pure Refl
    16 → pure RowPlus
    17 → pure Tag
    18 → pure TagEq
    19 → pure TypePlus
    20 → pure W
    21 → pure WUnwrap
    22 → pure WWrap
    23 → Int' <$> getNumDesc
    24 → IntAdd <$> getNumDesc
    25 → IntMul <$> getNumDesc
    26 → IntNeg <$> getNumDesc
    _ → fail "Unknown builtin tag"

-- TODO: More dense?
putNumDesc ∷ NumDesc → S.Put
putNumDesc = \case
  NumFin nonNeg bits → do
    S.putWord8 0
    putBool8 nonNeg
    putBits bits
  NumInf → S.putWord8 1

getNumDesc ∷ S.Get NumDesc
getNumDesc =
  S.getWord8 >>= \case
    0 → NumFin <$> getBool8 <*> getBits
    1 → pure NumInf
    _ → fail "Unknown num desc"

putBits ∷ Bits → S.Put
putBits =
  S.putWord8 . \case
    Bits8 → 0
    Bits16 → 1
    Bits32 → 2
    Bits64 → 3

getBits ∷ S.Get Bits
getBits = do
  tag ← S.getWord8
  case tag of
    0 → pure Bits8
    1 → pure Bits16
    2 → pure Bits32
    3 → pure Bits64
    _ → fail "Unknown bits tag"

putIdent ∷ Ident → S.Put
putIdent (Ident bs isOp) = putByteStringLen bs *> putBool8 isOp

getIdent ∷ S.Get Ident
getIdent = Ident <$> getByteStringLen <*> getBool8

putByteStringLen ∷ ByteString → S.Put
putByteStringLen bs = S.putWord32le (fromIntegral $ B.length bs) *> S.putByteString bs

getByteStringLen ∷ S.Get ByteString
getByteStringLen = do
  len ← fromIntegral <$> S.getWord32le
  S.getByteString len

putBool8 ∷ Bool → S.Put
putBool8 b = S.putWord8 $ if b then 1 else 0

getBool8 ∷ S.Get Bool
getBool8 = do
  b ← S.getWord8
  case b of
    0 → pure False
    1 → pure True
    _ → fail "Invalid boolean value"
