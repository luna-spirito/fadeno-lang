{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use const" #-}
module Compiler where

import Control.Algebra
import Control.Carrier.Empty.Church (runEmpty)
import Control.Carrier.Reader (ask, local, runReader)
import Control.Carrier.State.Church (State, StateC, evalState, get, put, runState)
import Control.Carrier.Writer.Church (WriterC, execWriter, tell)
import Control.Effect.Empty (empty)
import Control.Effect.State (modify, state)
import Data.ByteString.Char8 (pack)
import Data.Foldable (Foldable (foldr'))
import Data.IntMap.Strict qualified as IM
import Data.IntSet qualified as IS
import Data.RRBVector (Vector, drop, ifoldl, imap, replicate, reverse, splitAt, take, viewl, viewr, zip, (<|), (|>))
import GHC.Exts (IsList (..))
import NameGen (UsedNames, emptyUsedNames)
import NameGen qualified as N
import Parser (BlockF (..), BuiltinT (..), FieldsK (..), Ident (..), Lambda (..), Module (..), Quant (..), RefineK (..), Term (..), TermF (..), Vector' (..), nestedByP, regIdent, splitAt3, traverseTermF)
import RIO hiding (Vector, ask, drop, local, replicate, reverse, runReader, take, toList, zip)
import RIO.HashMap qualified as HM

-- KEEPS Import's
-- Unfortunately, not a rewrite', since this just erases & is not meant to simplify anything.
erase ∷ Vector Bool → Term → Term
erase reals =
  unTerm >>> \case
    Lam QEra _ body → erase (reals |> False) $ unLambda body
    Block (BlockLet _ QEra _ _ into) → erase (reals |> False) $ unLambda into
    Block (BlockRewrite _ into) → erase reals into
    AppErased f _ → erase reals f
    Var x → Term $ Var $ x - foldl' (\erased isReal → if isReal then erased else erased + 1) 0 (drop (length reals - x) reals)
    RefineGet i (_, Nothing) → erase reals $ Term $ Var i
    RefineGet _ (_, Just _) → Term $ FieldsLit (FRecord ()) []
    Refine (RefinePre _ann base) → erase reals base
    Refine (RefinePost base _ann) → erase reals base
    x → Term $ run $ traverseTermF (Identity . erase reals) (\n → Identity . Lambda . erase (reals <> replicate n True) . unLambda) x

listCaptures ∷ Word8 → Lambda Term → IntSet
listCaptures locals0 = run . execWriter . runReader @Int (fromIntegral locals0) . go . unLambda
 where
  go = fix \rec →
    unTerm >>> \case
      Var x → do
        locals ← ask @Int
        when (x >= locals) $ tell @IntSet [x - locals]
      x → void $ traverseTermF rec (\n → local @Int (+ n) . fmap Lambda . rec . unLambda) x

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
  | {- | Pi !Quant !Term !(Either (Ident, Lambda Term) Term)
    | Concat !Term !(Either (Ident, Lambda Term) Term)  deriving
    -}
    VImport !Int64
  deriving (Show, Eq)

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
data Code = CEmpty | CConst !Value | CGen !CodeGen

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

toCodeGen ∷ Code → CodeGen
toCodeGen = \case
  CConst x → instr $ IPush x
  CGen gen → gen
  CEmpty → pure ()
instance Semigroup Code where
  CEmpty <> b = b
  a <> CEmpty = a
  (toCodeGen → genA) <> (toCodeGen → genB) = CGen $ genA *> genB
instance Monoid Code where
  mempty = CEmpty

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
        (\_ → error "Internal error: Variable not found")
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

toConstM ∷ Code → Maybe Value
toConstM = \case
  CConst x → Just x
  _ → Nothing

toTagM ∷ Value → Maybe Word64
toTagM = \case
  VTag x → Just x
  _ → Nothing

-- compiles erased
compile' ∷ (Has Compile sig m) ⇒ Term → m Code
compile' =
  unTerm >>> \case
    (Block (BlockLet _ QEra _ _ _; BlockRewrite{}); ExVar{}; UniVar{}; Lam QEra _ _; AppErased{}; RefineGet{}; Refine (RefinePre{}; RefinePost{})) → undefined
    NumLit x → pure $ CConst $ VNum $ fromIntegral x
    TagLit tag → CConst . VTag <$> registry tag
    BoolLit x → pure $ CConst $ VBool x
    ListLit (Vector' entries) → do
      values0 ← for entries compile'
      pure case traverse toConstM values0 of
        Nothing → fold values0 <> CGen (instr $ IMkList $ fromIntegral $ length entries)
        Just values → CConst $ VList values
    FieldsLit (FRecord ()) (Vector' entries) → do
      kv0 ← for entries \(k, v) → (,) <$> compile' k <*> compile' v
      let n = fromIntegral $ length entries
      (values, mkRecord) ← case traverse (\(k, v) → (,v) <$> (toConstM k >>= toTagM)) kv0 of
        Nothing → pure (snd <$> kv0, foldMap fst kv0 <> CGen (instr $ IMkRecord $ fromIntegral $ length entries))
        Just kv → do
          (ts, values) ← mkTagSet kv
          pure (values, CGen $ instr $ IMkQRecord ts n)
      pure $ fold values <> mkRecord -- ts <> CGen (instr $ IMkRecord $ fromIntegral $ length entries)
    FieldsLit (FRow ()) _ → pure $ CConst VPanic
    BuiltinsVar → pure $ CConst VBuiltinsVar
    Builtin x → pure $ CConst $ VBuiltin x
    Lam QNorm _ body → do
      let
        (n, body') = getLambdaN body
        (captures, body'') = lambdaToClosure n body'
      bodyModule ← compile' $ unLambda body''
      let
        captures' = CGen . icopy <$> IS.toDescList captures
        closureVars = replicate (fromIntegral n + IS.size captures) True
        closure =
          CGen
            $ instr
            $ IClosure
              (fromIntegral $ IS.size captures)
              n
            $ execCodeGen closureVars
            $ toCodeGen bodyModule
      pure $ fold captures' <> closure
    ((unTerm → (unTerm → Term (Builtin If) `App` b) `App` t) `App` f) →
      compile' b >>= \case
        CConst (VBool b') → compile' if b' then t else f
        b' → do
          t' ← compile' t
          f' ← compile' f
          pure $ CGen do
            ctx ← get
            toCodeGen b'
            instr $ IIfElse (execCodeGen ctx $ toCodeGen t') (execCodeGen ctx $ toCodeGen f')
    App f a → do
      let (f', args) = getAppN (f, [a])
      args' ← for args compile'
      f'' ← compile' f'
      pure $ fold args' <> f'' <> CGen (instr $ IApp $ fromIntegral $ length args)
    Var x → pure $ CGen $ icopy x
    Block (BlockLet _n QNorm _ty val body) → do
      val' ← compile' val
      body' ← compile' $ unLambda body
      pure $ val' <> CGen (instr IPushVar) <> body' <> CGen (instr IPopVar)
    Refine (RefinePostTy{}) → pure $ CConst VPanic -- TODO
    Refine (RefinePreTy{}) → pure $ CConst VPanic -- TODO
    Import (fromMaybe (error "Internal error: unresolved import") → n) _ → pure $ CConst $ VImport $ fromIntegral n
    Sorry → pure $ CConst VPanic
    Pi{} → pure $ CConst VPanic -- TODO
    Concat{} → pure $ CConst VPanic -- TODO

type CompileResult = ((HashMap Ident Word64, HashMap TagSet Word64), Vector (Vector Instr))

compileModule ∷ Module → CompileResult
compileModule (Module m) =
  let (tags, (tagSets, codes)) = run $ runState @(HashMap Ident Word64) (curry pure) mempty $ runState @(HashMap TagSet Word64) (curry pure) mempty $ for m (compile' . erase [])
   in ((tags, tagSets), execCodeGen [] . toCodeGen <$> codes)

decompileModule ∷ CompileResult → Maybe Module
decompileModule ((tags0, tagSets0), instrs00) =
  run
    $ runEmpty (pure Nothing) (pure . Just)
    $ evalState @UsedNames emptyUsedNames
    $ Module
    <$> for instrs00 \i →
      evalState @(Vector Instr) i
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
    VImport x → pure $ Term $ Import (Just $ fromIntegral x) (pack $ show x)
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
          n ← regIdent <$> state N.gen
          res ←
            Term . Block . BlockLet (Right $ Just n) QNorm Nothing val . Lambda <$> do
              ctx0 ← get @(Vector (Maybe Term))
              put $ ctx0 |> Nothing
              scope <* put ctx0
          pushStack $ Just res
          scope
        ICopy i → do
          stack ← get @(Vector (Maybe Term))
          case splitAt3 (length stack - fromIntegral i - 1) stack of
            (_, Just t, after) → do
              let res = Just $ fromMaybe (Term $ Var 0) t `nestedByP` foldl' (\acc x → if isNothing x then acc + 1 else acc) 0 after
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
          body0 ←
            let lamStack = fmap Just captures <> replicate (fromIntegral argsN) Nothing
             in subdecompile lamStack lamInstrs
          argNames ← for @Vector [1 .. argsN] \_ → regIdent <$> state N.gen
          let res = foldr' (\n → Term . Lam QNorm (Just n) . Lambda) body0 argNames
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
