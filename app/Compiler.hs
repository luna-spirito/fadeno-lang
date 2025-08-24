-- This is absolutely horrfying and has strict limits which aren't even checked properly
module Compiler (compileFile) where

import Control.Algebra
import Control.Carrier.State.Church (State, StateC, get, put, runState)
import Control.Carrier.Writer.Church (Writer, censor, execWriter, tell)
import Data.IntMap.Strict (toAscList)
import Data.IntMap.Strict qualified as IM
import Data.IntSet (maxView, member)
import Data.List (sortBy)
import Data.RRBVector (Vector, imap, replicate, splitAt, viewr, zip, (<|), (|>))
import Data.Serialize qualified as S
import GHC.Exts (IsList (..))
import Normalize (rewrite)
import Parser (Bits (..), BlockT (..), BuiltinT (..), Ident (..), Lambda (..), NumDesc (..), Quant (..), Term (..), Vector' (..), parseFile)
import RIO hiding (Vector, replicate, toList, zip)
import RIO.ByteString qualified as B
import RIO.HashMap qualified as HM
import RIO.List (stripSuffix)

-- Unfortunately, not a rewrite', since this just erases & is not meant to
-- simplify anything
erase ∷ Vector Bool → Term → Term
erase reals = \case
  NumLit x → NumLit x
  TagLit tag → TagLit tag
  BoolLit x → BoolLit x
  ListLit entries → ListLit $ erase reals <$> entries
  RecordLit fields → RecordLit $ bimap (erase reals) (erase reals) <$> fields
  Lam QNorm n body → Lam QNorm n $ Lambda $ erase (True <| reals) $ unLambda body
  Lam QEra _ body → erase (False <| reals) $ unLambda body
  App f a → App (erase reals f) (erase reals a)
  AppErased f _a → erase reals f
  Var x →
    let (potentiallyErased, _) = splitAt x reals
     in Var $ x - foldl' (\acc real → if real then acc else acc + 1) 0 potentiallyErased
  BuiltinsVar → BuiltinsVar
  Builtin x → Builtin x
  Block (BlockLet QNorm n _ty val body) → Block $ BlockLet QNorm n Nothing val $ Lambda $ erase (True <| reals) $ unLambda body
  Block (BlockLet QEra _ _ _ body) → erase (False <| reals) $ unLambda body
  Block (BlockRewrite _ body) → erase reals body
  Sorry → Sorry
  Pi q inT outT → Pi q (erase reals inT) (either (Left . fmap \bod → Lambda $ erase (True <| reals) $ unLambda bod) (Right . erase reals) outT)
  Concat aT bT → Concat (erase reals aT) (either (Left . fmap \bod → Lambda $ erase (True <| reals) $ unLambda bod) (Right . erase reals) bT)
  ExVar{} → undefined
  UniVar{} → undefined

listCaptures ∷ Lambda Term → IntSet
listCaptures =
  runIdentity
    . execWriter
    . rewrite
      (\_ → (+ 1))
      (+ 1)
      ( \t locals →
          Nothing <$ case t of
            Var x → if x >= locals then tell @IntSet [x - locals] else pure ()
            _ → pure ()
      )
      1 -- Local bindings
    . unLambda

-- Identifies captured bindings and erases non-captured variables
-- Proper type: Fun (n : Int) (Lambda n Term) -> { .captures: IntSet | .erased: Lambda n Term }
lambdaToClosure ∷ Int → Lambda Term → (IntSet, Lambda Term)
lambdaToClosure n orig =
  let
    captures = listCaptures orig
    reals = imap (\i () → i `member` captures) (replicate (maybe 0 fst $ maxView captures) ())
   in
    (captures, Lambda $ erase (replicate n True <> reals) $ unLambda orig)

-- A helper function that identifies trivially nested lambdas `\x y z. ...`
-- Proper type: Fun (Lambda 1 Term) -> (self : { .n : Int } \/ { .lam : Lambda self.n Term })
getLambdaN ∷ Lambda Term → (Int, Lambda Term)
getLambdaN lam = case unLambda lam of
  Lam QNorm _ body → bimap (+ 1) id $ getLambdaN body
  body → (1, Lambda body)

getAppN ∷ (Term, Vector Term) → (Term, Vector Term)
getAppN (App f a, args) = getAppN (f, a <| args)
getAppN (f, args) = (f, args)

data Value
  = VNum !Integer
  | VTag !Int
  | VBool !Bool
  | VList !(Vector Value)
  | VRecord !Int !(Vector Value)
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
-}
data Instr
  = IPush !Value
  | IPushVar
  | IPopVar !Int
  | ICopyVar !Int
  | IApp !Int
  | IClosure !Int ![Int] !Int -- arguments, captured, ops
  | IIf !Int
  | IElse !Int
  | IMkList !Int
  | IMkRecord !Int -- n values followed by n tags
  deriving (Show, Eq)

type Compile = State (HashMap Ident Int) :+: Writer (Vector Instr)

instr ∷ (Has Compile sig m) ⇒ Instr → m ()
instr x = tell @(Vector Instr) [x]

registry ∷ ∀ r sig m. (Has (State (HashMap r Int)) sig m, Hashable r) ⇒ r → m Int
registry val = do
  toI ← get @(HashMap r Int)
  case HM.lookup val toI of
    Just i → pure i
    Nothing → do
      let i = HM.size toI
      put $ HM.insert val i toI
      pure i

-- compiles erased
compile' ∷ (Has Compile sig m) ⇒ Term → m ()
compile' = \case
  NumLit x → instr $ IPush $ VNum x
  TagLit tag → instr . IPush . VTag =<< registry tag
  BoolLit x → instr $ IPush $ VBool x
  ListLit (Vector' entries) → do
    for_ entries compile'
    instr $ IMkList $ length entries
  RecordLit (Vector' entries) → do
    for_ entries \(_, v) → compile' v
    for_ entries \(k, _) → compile' k
    instr $ IMkRecord $ length entries
  Lam QNorm _ body → do
    let (n, body') = getLambdaN body
    let (captures, body'') = lambdaToClosure n body'
    censor @(Vector Instr)
      ( \bodyInstr → do
          IClosure n (toList captures) (length bodyInstr) <| bodyInstr
      )
      $ compile'
      $ unLambda body''
  Lam QEra _ _ → undefined
  (Builtin If `App` b `App` t `App` f) → do
    compile' b
    censor @(Vector Instr) (\tInstr → IIf (length tInstr) <| tInstr) $ compile' t
    censor @(Vector Instr) (\fInstr → IElse (length fInstr) <| fInstr) $ compile' f
  App f a → do
    let (f', args) = getAppN (f, [a])
    compile' f'
    for_ args compile'
    instr $ IApp $ length args
  AppErased{} → undefined
  Var x → instr $ ICopyVar x
  BuiltinsVar → instr $ IPush VBuiltinsVar
  Builtin x → instr $ IPush $ VBuiltin x
  Block (BlockLet QNorm _n _ty val body) → do
    compile' val
    instr IPushVar
    compile' $ unLambda body
    instr $ IPopVar 1
  Block (BlockLet QEra _ _ _ _) → undefined
  Block (BlockRewrite _ _) → undefined
  Sorry → instr $ IPush VPanic
  Pi q inT outT → error "TODO"
  Concat aT bT → error "TODO"
  ExVar{} → undefined
  UniVar{} → undefined

getNPushes ∷ Int → Vector Instr → Maybe (Vector Instr, Vector Value)
getNPushes 0 iis = Just (iis, [])
getNPushes n iis = case viewr iis of
  Just (is, IPush val) → fmap (|> val) <$> getNPushes (n - 1) is
  _ → Nothing

type TagProfile = IntMap Int

organizeFields ∷ Vector (Int, Value) → IntMap (Vector Value)
organizeFields = foldl' (\acc (k, v) → IM.alter (Just . (|> v) . fromMaybe []) k acc) mempty

-- Merges lists, records, pops.
merge ∷ Vector Instr → (HashMap TagProfile Int, Vector Instr)
merge = runIdentity . runState (curry pure) mempty . foldM push1 []
 where
  push1 ∷ Vector Instr → Instr → StateC (HashMap TagProfile Int) Identity (Vector Instr)
  push1 origInstrs = \case
    IMkList n
      | Just (instrs, vals) ← getNPushes n origInstrs →
          pure $ instrs |> IPush (VList vals)
    IMkRecord n
      | Just (origInstrsWithoutTags, tagVals) ← getNPushes n origInstrs
      , Just tags ← for tagVals \case
          VTag t → Just t
          _ → Nothing -- This actually shouldn't be possible for proper programs
      , Just (instrs, vals) ← getNPushes n origInstrsWithoutTags →
          do
            let organized = organizeFields (zip tags vals)
            i ← registry (length <$> organized)
            pure $ instrs |> IPush (VRecord i $ join $ fromList $ fmap snd $ toAscList $ organized)
    IPopVar n2
      | Just (instrs, IPopVar n1) ← viewr origInstrs →
          pure $ instrs |> IPopVar (n1 + n2)
    x → pure $ origInstrs |> x

-- Doesn't check
registryToList ∷ (Hashable r) ⇒ HashMap r Int → [r]
registryToList = fmap fst . sortBy (\a b → compare (snd a) (snd b)) . toList

-- TODO: Check all fromIntegral!

putB ∷ S.Putter ByteString
putB b = S.putWord64le (fromIntegral $ B.length b) *> S.putByteString b

putBool ∷ S.Putter Bool
putBool b = S.putWord8 if b then 1 else 0

putTagProfile ∷ S.Putter TagProfile
putTagProfile = traverse_ (\(k, v) → S.putWord64le (fromIntegral k) *> S.putWord64le (fromIntegral v)) . toAscList

putValue ∷ S.Putter Value
putValue = \case
  VNum x → S.putWord8 0 *> S.putWord64le (fromIntegral x)
  VTag x → S.putWord8 1 *> S.putWord64le (fromIntegral x)
  VBool x → S.putWord8 2 *> putBool x
  VList l → S.putWord8 3 *> S.putWord64le (fromIntegral $ length l) *> for_ (toList l) putValue
  VRecord i values → S.putWord8 4 *> S.putWord64le (fromIntegral i) *> for_ values putValue
  -- VLam 5
  VBuiltinsVar → S.putWord8 6
  VBuiltin b → S.putWord8 7 *> putBuiltin b
  VPanic → S.putWord8 8

putBuiltin ∷ S.Putter BuiltinT
putBuiltin =
  S.putWord8 . \case
    Tag → 0
    Row → 1
    Record → 2
    List → 3
    Bool → 4
    TypePlus → 5
    Eq → 6
    Refl → 7
    RecordGet → 8
    RecordKeepFields → 9
    RecordDropFields → 10
    ListLength → 11
    ListIndexL → 12
    NatFold → 13
    If → 14
    IntGte0 → 15
    IntEq → 16
    IntNeq → 17
    TagEq → 18
    W → 19
    Wrap → 20
    Unwrap → 21
    Never → 22
    Any' → 23
    IntNeg → 24
    Add numDesc → 25 + encodeNumDesc numDesc
    Sub numDesc → 35 + encodeNumDesc numDesc
    Num numDesc → 45 + encodeNumDesc numDesc

encodeNumDesc ∷ NumDesc → Word8
encodeNumDesc (NumDesc isNonNeg bits) =
  let bitsVal = case bits of
        Bits8 → 0
        Bits16 → 1
        Bits32 → 2
        Bits64 → 3
        BitsInf → 4
      nonNegVal = if isNonNeg then 5 else 0
   in bitsVal + nonNegVal

putInstr ∷ S.Putter Instr
putInstr = \case
  IPush v → S.putWord8 0 *> putValue v
  IPushVar → S.putWord8 1
  IPopVar n → S.putWord8 2 *> S.putWord8 (fromIntegral n)
  ICopyVar n → S.putWord8 3 *> S.putWord8 (fromIntegral n)
  IApp n → S.putWord8 4 *> S.putWord8 (fromIntegral n)
  IClosure a c o →
    S.putWord8 5
      *> S.putWord8 (fromIntegral a)
      *> S.putWord8 (fromIntegral $ length c)
      *> S.putListOf (S.putWord8 . fromIntegral) c
      *> S.putWord32le (fromIntegral o)
  IIf n → S.putWord8 6 *> S.putWord32le (fromIntegral n)
  IElse n → S.putWord8 7 *> S.putWord32le (fromIntegral n)
  IMkList n → S.putWord8 8 *> S.putWord32le (fromIntegral n)
  IMkRecord n → S.putWord8 9 *> S.putWord32le (fromIntegral n)

compileFile ∷ FilePath → IO ()
compileFile file = do
  parsed ← parseFile file
  let (tags, unmerged) = runIdentity $ runState @(HashMap Ident Int) (curry pure) mempty $ execWriter @(Vector Instr) $ compile' parsed
  let (profiles, merged) = merge unmerged
  writeFileBinary (fromMaybe file (stripSuffix ".fad" file) <> ".fadobj") $ S.runPut do
    S.putListOf (\(Ident n op) → putB n *> S.put op) $ registryToList tags
    S.putListOf putTagProfile $ registryToList profiles
    S.putListOf putInstr $ toList merged
