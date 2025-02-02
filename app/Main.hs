{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Main where

import Control.Carrier.State.Church
import Control.Effect.Fresh (fresh, Fresh)
import Control.Effect.Writer (Writer, censor, listen, tell)
import Data.Kind (Type)
import Data.List (uncons, intercalate)
import GHC.Exts (IsList (..))
import Parser qualified as P
import RIO hiding (link, ask, runReader, toList)
import RIO.HashMap qualified as HM
import qualified Data.IntMap.Strict as IM
import qualified RIO.Partial as P
import Control.Carrier.Reader (ReaderC, runReader)
import Control.Effect.Reader (ask)
import Control.Algebra
import Control.Carrier.Empty.Church (runEmpty)
import qualified Control.Effect.Empty as E
import Type.Reflection ((:~:) (..))
import qualified RIO.Vector as V
import Control.Effect.Lift (Lift, sendIO, sendM)
import Control.Carrier.Fresh.Church (FreshC, evalFresh)
import Control.Carrier.Writer.Church (runWriter, execWriter, WriterC)
import RIO.Seq  (Seq(..))
import Data.Bits (unsafeShiftL, (.|.), unsafeShiftR, (.&.))
import Data.Serialize (putWord8, PutM, putWord32be, putWord64be, execPut, runPutMBuilder, putBuilder)
import Control.Carrier.Accum.Church (evalAccum)
import Control.Carrier.Lift (LiftC, runM)
import qualified RIO.Seq as S
import Data.ByteString.Builder (toLazyByteString)
import Control.Effect.Accum (look, add)
import qualified Data.ByteString.Char8 as BS
import System.IO (print)

{-
Whenever a node interacts with a negative package, DO NOT UNWRAP.
Instead, create a new, specialized package.

Also, maybe YES sub-packages?, but NO deep substitutions. This messes things up.
What could help is: BI-DIRECTIONALLY phase primary ports through custom node's auxiliary?
This could help even in regular code I guess.
\x
  y = [3, 4, x]
  z = (9, y)
  w = (10, y)
  in (z, w)
... will automatically inline `y`.

So, let's first separate tags and ports?

\y ->
  // x = +> (y, y)
  x = (y, y)
  in MkPair x x
  
builtins/rec \rec ->
  \y -> if y == 0
    then y*rec (y-1)
    else 0

EDIT: instead of "phasing" primary ports, just fix the entry point and "suck in" all the other nodes.
EDIT: "phasing/sucking in/out" is not that bad since it increases optimality, but it as well reduces the compilation
capabilities by reducing the amount of available information.
"Phasing in" is clearly not as bad as "phasing out", but I'm not sure it's worth the effort and it still can yield worse performance
in some edge cases (ex. partial erasure), although usually it's better.

28.12.24: Phasing in/out, while could be a good thing for optimality, is not always this way.
We'd better stick to the approach of "trusting the programmer", at least for now.
Whatever programmer says to be the node, will be the node, with no "extra"s or "exclusion"s.
Also, we package local variables as a transparent optimization, but we don't guarantee doing this or doing this the best way, but
we do guarantee that we do it only when it preserves optimality.

28.12.24: Solution:
No phasings. Instead, each time a specialisation occurs (i. e. you interact with negative package), DO NOT UNWRAP it.
-}

-- TODO: Currently identifiers with `/` are reserved.
-- Correct type-checking also depends on this. This is absolutely horrible.
-- TODO: just calm down and use freaking substitutions.
-- You can't guarantee correctness of the mess you've written if you
-- continue to do things this way.

newtype RevList a = UnsafeRevList [a] deriving (Functor, Show)

instance Semigroup (RevList a) where
  UnsafeRevList a <> UnsafeRevList b = UnsafeRevList $ b <> a
instance Monoid (RevList a) where
  mempty = []

revSnoc ∷ RevList a → a → RevList a
revSnoc (UnsafeRevList ls) x = UnsafeRevList $ x : ls

revUnsnoc ∷ RevList a → Maybe (RevList a, a)
revUnsnoc (UnsafeRevList x) = (\(v, l) → (UnsafeRevList l, v)) <$> uncons x

instance IsList (RevList a) where
  type Item (RevList a) = a
  fromList ls = UnsafeRevList $ reverse ls
  toList (UnsafeRevList ls) = reverse ls

-- Check

-- | "Type of" TermT
data TTermT = T P.TermT | Kind deriving Show -- Actually should be merged with TermT definition, but Haskell.

-- | Context stores values and the type of introduced bindings.
type CtxT = HashMap P.Ident (Maybe P.TermT, TTermT)

data SEntry = SScope | SExVar
-- | For meta-variables
type SolveM = StateC (IntMap [P.MetaVar']) (FreshC IO)

freshIdent :: SolveM P.Ident
freshIdent = P.UIdent <$> fresh

scoped :: SolveM P.TermT → SolveM P.TermT
scoped act = do
  modify @(IntMap [P.MetaVar']) \scopes → IM.insert (IM.size scopes) [] scopes
  ty ← act
  exs ← state @(IntMap [P.MetaVar']) \scopes →
    (IM.deleteMax scopes, snd $ fromMaybe (error "Internal error: Scope disappeared") $ IM.lookupMax scopes)
  foldM
    (\ty' (P.MetaVar' x) → do
      var ← fresh
      let var' = P.Ident $ BS.pack $ "/" <> show var
      sendIO $ writeIORef x $ Left $ P.Var var'
      -- TODO: not just Ty!
      pure $ P.Forall var' P.Ty ty')
    ty
    exs

-- Assumes that all existentias are resolved if they are ever used.
scoped_ :: SolveM a → SolveM a
scoped_ act = do
  modify @(IntMap [P.MetaVar']) \scopes → IM.insert (IM.size scopes) [] scopes
  res ← act
  modify @(IntMap [P.MetaVar']) IM.deleteMax
  pure res

delMeta :: Int → P.MetaVar' → SolveM ()
delMeta scope var =
  modify @(IntMap [P.MetaVar']) \scopes →
    IM.adjust (filter (/= var)) scope scopes

insMeta :: Int → P.MetaVar' → SolveM ()
insMeta scope var =
  modify @(IntMap [P.MetaVar']) \scopes →
    IM.adjust (var:) scope scopes

pushExVarInto :: Int → SolveM P.MetaVar'
pushExVarInto scope = do 
  metaVar' ← fmap P.MetaVar' $ sendIO $ newIORef $ Right $ scope
  insMeta scope metaVar'
  pure metaVar'

pushExVar :: SolveM P.TermT
pushExVar = do
  scope ← (\x → x - 1) . IM.size <$> get @(IntMap [P.MetaVar'])
  P.MetaVar <$> pushExVarInto scope

writeMeta :: Int → P.MetaVar' → P.TermT → SolveM ()
writeMeta scope (P.MetaVar' var) val = do
  sendIO $ writeIORef var $ Left val
  delMeta scope (P.MetaVar' var)

instMeta :: Int → P.MetaVar' → P.TermT → SolveM ()
instMeta scope1 (P.MetaVar' var1) = instMeta' where
  instMeta' = \case
    P.MetaVar (P.MetaVar' var2)
      | var1 == var2 → pure ()
      | otherwise → sendIO (readIORef var2) >>= \case
        Left t → instMeta scope1 (P.MetaVar' var1) t
        Right scope2 →
          let (early, (lateScope, late)) = if scope1 <= scope2
              then (var1, (scope2, var2))
              else (var2, (scope1, var1))
          in writeMeta lateScope (P.MetaVar' late) $ P.MetaVar $ P.MetaVar' early
    P.Var x → writeMeta scope1 (P.MetaVar' var1) $ P.Var x
    P.U32 → writeMeta scope1 (P.MetaVar' var1) P.U32
    P.Pi inNameM inT outT → do
      a ← pushExVarInto scope1
      b ← pushExVarInto scope1
      writeMeta scope1 (P.MetaVar' var1) $ P.Pi inNameM (P.MetaVar a) (P.MetaVar b)
      instMeta scope1 a inT *> instMeta scope1 b outT
    x → error $ "instMeta " <> show (P.pTerm 0 x)

normalize :: Has (Lift IO) sig m ⇒ HashMap P.Ident P.TermT → P.TermT → m P.TermT
normalize binds = \case
  P.Let ((name, _, val) :| bs) into → do
    val' ← normalize binds val
    normalize
      (HM.insert name val' binds)
      case bs of
        [] → into
        (b1:b2) → P.Let (b1 :| b2) into
  P.Lam arg bod → P.Lam arg <$> normalize binds bod
  P.Op a op b → error "todo"
  P.App f a → do
    a' ← normalize binds a
    f' ← normalize binds f
    case f' of
      P.Lam arg bod → normalize (HM.insert arg a' binds) bod
      _ → pure $ P.App f' a'
  P.NatLit x → pure $ P.NatLit x
  P.Var x → pure $ case HM.lookup x binds of
    Nothing → P.Var x
    Just x' → x'
  P.Forall x a b → P.Forall x <$> normalize binds a <*> normalize (HM.delete x binds) b
  P.U32 → pure P.U32
  P.Pi aM b c → P.Pi aM <$> normalize binds b <*> normalize (maybe id HM.delete aM binds) c
  P.Ty → pure P.Ty
  old@(P.MetaVar (P.MetaVar' var)) → sendIO (readIORef var) >>= \case
    Left t → normalize binds t
    Right _ → pure old

data InferMode a where
  Infer :: InferMode TTermT
  Check :: TTermT → InferMode ()

-- (\f. \x. f (f x))
infer :: CtxT → P.TermT → InferMode a → SolveM a
infer ctx = curry \case
  (P.Let ((name, tyM, val) :| bs) into, mode) → do
    let normCtx = HM.mapMaybe fst ctx
    ty ← case tyM of
      Nothing → infer ctx val Infer
      Just ty → do
        ty' ← T <$> normalize normCtx ty
        infer ctx val $ Check ty'
        pure ty'
    val' ← normalize normCtx val
    -- TODO: annotations. Normalize'em
    infer
      (HM.insert name (Just val', ty) ctx)
      (case bs of
        [] → into
        (b1:b2) → P.Let (b1 :| b2) into)
      mode
  (P.Lam arg bod, Infer) →
    T <$> scoped do
      inT ← pushExVar
      outT ← infer (HM.insert arg (Nothing, T inT) ctx) bod Infer
      pure case outT of
        Kind → error ""
        T outT' → P.Pi Nothing inT outT'
  (P.Lam arg bod, Check (T (P.Pi inNameM inT outT))) → do
    (val, outT') ← case inNameM of
      Nothing → pure (Nothing, outT)
      Just inName → do
        arg' ← freshIdent
        outT' ← normalize (HM.singleton inName $ P.Var arg') outT
        pure (Just $ P.Var arg', outT')
    infer (HM.insert arg (val, T inT) ctx) bod $ Check $ T outT'
  (P.Op a _op b, Infer) → do
    infer ctx a $ Check $ T P.U32
    infer ctx b $ Check $ T P.U32
    pure $ T P.U32
  (P.App f a, Infer) → do
    let
      inferApp = \case
        T (P.Pi inNameM inT outT) → do
          infer ctx a $ Check $ T inT
          case inNameM of
            Nothing → pure outT
            Just inName → do
              a' ← normalize (HM.mapMaybe fst ctx) a
              normalize (HM.singleton inName a') outT
        T (P.MetaVar (P.MetaVar' var)) → sendIO (readIORef var) >>= \case
          Left t → inferApp $ T t
          Right scope → do
            -- I'm not satisfied by this solution, but instMeta solution is
            -- even more verbose since it accepts full TermT as input.
            inT ← P.MetaVar <$> pushExVarInto scope
            outT ← P.MetaVar <$> pushExVarInto scope
            writeMeta scope (P.MetaVar' var) (P.Pi Nothing inT outT)
            infer ctx a $ Check $ T inT
            pure outT
        T (P.Forall xName P.Ty bod) → scoped do -- not just Ty!
          x ← pushExVar
          bod' ← normalize (HM.singleton xName x) bod
          inferApp $ T bod'
        t → error $ "inferApp " <> show t
    fmap T . inferApp =<< infer ctx f Infer
  (P.NatLit _, Infer) → pure $ T P.U32
  (P.Var x, Infer) → case HM.lookup x ctx of
    Nothing → error $ "Unknown var " <> show x
    Just (_, ty) → pure ty
  -- (x, Infer) → error $ "TODO " <> show x
  (term, Check c) → do
    ty ← infer ctx term Infer
    -- traceM $ (case ty of
    --   Kind → "Kind"
    --   T t' → tshow $ P.pTermT 0 t') <> " <: " <>
    --   (case c of
    --     Kind → "Kind"
    --     T c' → tshow $ P.pTermT 0 c')
    subtype ty c

-- | a <: b
subtype :: TTermT -> TTermT -> SolveM ()
subtype = curry \case
  (T (P.MetaVar a), T bT) → subtypeMeta subtype a bT
  (T aT, T (P.MetaVar b)) → subtypeMeta (flip subtype) b aT
  (T (P.Var (P.UIdent a)), T (P.Var (P.UIdent b)))
    | a == b → pure ()
  (T (P.Forall xName P.Ty aT), T bT) → do
    x' ← P.Var <$> freshIdent
    aT' ← normalize (HM.singleton xName x') aT
    subtype (T aT') (T bT)
  (T aT, T (P.Forall xName P.Ty bT)) → scoped_ do -- TODO: not just Ty
    xTy ← pushExVar
    bT' ← normalize (HM.singleton xName xTy) bT
    subtype (T aT) (T bT')
  (T (P.Pi aNameM a b), T (P.Pi cNameM c d)) → do
    e ← P.Var <$> freshIdent
    b' ← maybe pure (\aName → normalize $ HM.singleton aName e) aNameM b
    d' ← maybe pure (\cName → normalize $ HM.singleton cName e) cNameM d
    subtype (T c) (T a)
    subtype (T b') (T d')
  (T P.U32, T P.U32) → pure ()
  (aT, bT) → error $ show aT <> " <: " <> show bT
  where
    subtypeMeta subf (P.MetaVar' a) bT = 
      sendIO (readIORef a) >>= \case
        Left aT → subf (T aT) $ T bT
        Right scope → instMeta scope (P.MetaVar' a) bT

runSolveM :: SolveM a → IO a
runSolveM = evalFresh 0 . evalState mempty

checkFile :: FilePath → IO ()
checkFile file = do
  term ← P.parseFileOrDie file
  ttermt ← runSolveM $ infer [] term Infer
  case ttermt of
    Kind → print @String "Kind"
    T ty → P.printTerm ty

-- IC

data Polarity = Pos | Neg

-- data PortId (p :: Polarity) = PortId !Int
-- data WireId = WireId !Int
-- type Wire = Either (Node Neg) (Node Pos)

-- | And end of a wire.
data WireEnd (p :: Polarity) = WireEnd !Word32
  deriving Show
type AnyWireEnd = Either (WireEnd Neg) (WireEnd Pos)

data Node :: Polarity → Type where
  App :: !(WireEnd Neg) → !(WireEnd Pos) → Node Neg
  Lam :: !(WireEnd Pos) → !(WireEnd Neg) → Node Pos
  Dup ∷ !Word32 → !(WireEnd Pos) → !(WireEnd Pos) → Node Neg
  Sup :: !Word32 → !(WireEnd Neg) → !(WireEnd Neg) → Node Pos
  Word32 :: !Word32 → Node Pos
  Op2 :: !P.OpT → !(WireEnd Pos) → !(WireEnd Neg) → Node Neg
  Op1 :: !P.OpT → !(WireEnd Pos) → !(Word32) → Node Neg
  Era :: Node Neg
  Nul :: Node Pos
  StaticHeavy :: !HeavyId → !(Vector AnyWireEnd) → Node Pos
  Debug :: Node Neg

instance Show (Node a) where
  show = \case
    App {} → "App"
    Lam {} → "Lam"
    Dup {} → "Dup"
    Sup {} → "Sup"
    Word32 {} → "Word32"
    Op2 {} → "Op2"
    Op1 {} → "Op1"
    Era {} → "Era"
    Nul {} → "Nul"
    StaticHeavy {} → "StaticHeavy"
    Debug {} → "Debug"

type AnyNode = Either (Node Neg) (Node Pos)

newtype HeavyId = HeavyId Word32

-- | Extension over WireEnd that also allows to serialise wires to primary ports;
-- wires to heavy's auxiliary ports, both persistent and temporary (the ones used for multi-operand nodes introduced by -op1-op2+>).
data HeavyWireEnd (pol :: Polarity)
  = HWAux !(WireEnd pol)
  | HWPri !Word32

type AnyHeavyWireEnd = Either (HeavyWireEnd Neg) (HeavyWireEnd Pos)

-- Format of heavy package differs between -lang and -jit.
-- First elements of the auxs vector contains persistent aux, last — temporary ones. In normal order.
data StaticHeavyPackage = StaticHeavyPackage !Int !Bool !(HeavyWireEnd Neg) !(Vector AnyHeavyWireEnd) !(Vector AnyNode)

type Eval = State (IntMap (Either Word32 AnyNode)) :+: State (IntMap StaticHeavyPackage) :+: Fresh :+: Lift IO

newWire :: Has Eval sig m => m (WireEnd Neg, WireEnd Pos)
newWire = do
  wireId ← fromIntegral <$> fresh
  pure (WireEnd wireId, WireEnd wireId)

type family OppositePolarity a :: Polarity where
  OppositePolarity Pos = Neg
  OppositePolarity Neg = Pos
class DecPolarity (a :: Polarity) where
  decPolarity :: Proxy a → Either (a :~: Neg) (a :~: Pos)

instance DecPolarity Neg where
  decPolarity _ = Left Refl
instance DecPolarity Pos where
  decPolarity _ = Right Refl

travPorts :: Applicative f ⇒ (forall b. DecPolarity b => WireEnd b → f (WireEnd b)) → Node a → f (Node a)
travPorts f = \case
  App a b → App <$> f a <*> f b
  Lam a b → Lam <$> f a <*> f b
  Dup dupl a b → Dup dupl <$> f a <*> f b
  Sup dupl a b → Sup dupl <$> f a <*> f b
  Word32 w → pure $ Word32 w
  Op2 op a b → Op2 op <$> f a <*> f b
  Op1 op a w → (\a' → Op1 op a' w) <$> f a
  Era → pure Era
  Nul → pure Nul
  StaticHeavy heavyId auxs  → StaticHeavy heavyId <$> for auxs (either (fmap Left . f) (fmap Right . f))
  Debug → pure Debug

-- Destructive
contractWire :: forall a sig m. (DecPolarity a, Has Eval sig m) => WireEnd a → m (Word32, Maybe (Node (OppositePolarity a)))
contractWire (WireEnd wire0Id) = do
  wire0 ← IM.lookup @(Either Word32 AnyNode) (fromIntegral wire0Id) <$> get
  case wire0 of
    Just (Left wireId) → do
      modify $ IM.delete @(Either Word32 AnyNode) $ fromIntegral wire0Id
      contractWire $ WireEnd @a wireId
    Just (Right a) → pure (wire0Id, Just case (a, decPolarity $ Proxy @a) of
        (Left a', Right Refl) → a'
        (Right a', Left Refl) → a'
        _ → error $ "impossible " <> show wire0Id
      )
    Nothing → pure (wire0Id, Nothing)

-- TODO: totality
link :: Has Eval sig m => WireEnd Neg → WireEnd Pos → m ()
link l0Id r0Id = do
  (lId, l) ← contractWire l0Id
  (rId, r) ← contractWire r0Id
  case (l, r) of
    (Nothing, _) → do
      modify $ IM.insert @(Either Word32 AnyNode) (fromIntegral lId) $ Left rId
    (Just _, Nothing) → do
      modify $ IM.insert @(Either Word32 AnyNode) (fromIntegral rId) $ Left lId
    (Just a, Just b) → do
      for_ @[] [lId, rId] $ modify . IM.delete @(Either Word32 AnyNode) . fromIntegral
      eval b a
 
move :: forall a sig m. (Has Eval sig m, DecPolarity a) ⇒ Node a → WireEnd a → m ()
move a wire0Id = do
  (wireId, wire) ← contractWire wire0Id
  case wire of
    Nothing → do
      modify $ IM.insert @(Either Word32 AnyNode) (fromIntegral wireId) $ Right $ either (\Refl → Left a) (\Refl → Right a) $ decPolarity $ Proxy @a
    Just b → do
      modify $ IM.delete @(Either Word32 AnyNode) $ fromIntegral wireId
      uncurry eval $ either (\Refl → (a, b)) (\Refl → (b, a)) $ decPolarity $ Proxy @a

newtype TupC m a = TupC (forall (r :: Type). ((a, a) -> m r) -> m r)
  deriving Functor

instance Applicative (TupC m) where
  pure a = TupC \r → r (a, a)
  TupC f <*> TupC a = TupC \r →
    f \(f1, f2) → a \(a1, a2) → r (f1 a1, f2 a2)

dup :: forall a sig m. (DecPolarity a, Has Eval sig m) => WireEnd a → TupC (ReaderC Word32 m) (WireEnd a)
dup orig = TupC \r → do
  (d1, s1) ← lift newWire
  (d2, s2) ← lift newWire
  l ← ask @Word32
  case decPolarity $ Proxy @a of
    Left Refl → do
      move (Dup l s1 s2) orig
      r (d1, d2)
    Right Refl → do
      move (Sup l d1 d2) orig
      r (s1, s2)

runComm :: Has Eval sig m => Word32 → TupC (ReaderC Word32 m) a → m (a, a)
runComm l (TupC act) = runReader l $ act pure

runDup :: (Has Eval sig m, DecPolarity a) ⇒ Word32 → WireEnd a → WireEnd a → TupC (ReaderC Word32 m) (Node a) → m ()
runDup l dp1 dp2 act = do
  (d1, d2) ← runComm l act
  move d1 dp1
  move d2 dp2

primary :: forall a sig m. (DecPolarity a, Has Eval sig m) ⇒ Node a → m (WireEnd (OppositePolarity a))
primary n = do
  (neg, pos) ← newWire
  case decPolarity $ Proxy @a of
    Left Refl → move n neg $> pos
    Right Refl → move n pos $> neg

packHV :: HeavyWireEnd a → WireEnd a
packHV hv =
  let (tag, val) = case hv of
        HWAux (WireEnd v) → (0, v)
        HWPri v → (1, v)
        -- HWPersistentAux v → (2, v)
        -- HWTemporaryAux v → (3, v)
  in WireEnd $ (tag `unsafeShiftL` 31) .|. val

unpackHV :: WireEnd a → HeavyWireEnd a
unpackHV (WireEnd x) =
  let (tag, val) = (x `unsafeShiftR` 31, x .&. 0x7FFFFFFF)
  in case tag of
    0 → HWAux $ WireEnd val
    1 → HWPri val
    _ → error "unknown tag"

instHeavy :: forall sig m. Has Eval sig m => HeavyId → Vector AnyWireEnd → m (WireEnd Neg)
instHeavy (HeavyId heavyId) auxs = do
  StaticHeavyPackage persAuxsLen hasResAux mainWire auxWires ns ← P.fromJust . IM.lookup @StaticHeavyPackage (fromIntegral heavyId) <$> get
  let
    write :: forall a. DecPolarity a => Word32 → StateC (IntMap Word32) m (Node a)
    write i = case (decPolarity $ Proxy @a, P.fromJust $ ns V.!? fromIntegral i) of
      (Left Refl, Left n) → travPorts r n
      (Right Refl, Right n) → travPorts r n
      _ → error "impossible"
    
    r :: forall a. DecPolarity a ⇒ WireEnd a → StateC (IntMap Word32) m (WireEnd a)
    r = r' . unpackHV

    r' :: forall a. DecPolarity a ⇒ HeavyWireEnd a → StateC (IntMap Word32) m (WireEnd a)
    r' hw0 = case hw0 of
      HWAux (WireEnd wire0Id) → do
        wireIdM ← IM.lookup (fromIntegral wire0Id) <$> get
        WireEnd <$> case wireIdM of
          Nothing → do
            wireId ← fresh
            modify $ IM.insert @Word32 (fromIntegral wire0Id) $ fromIntegral wireId
            pure $ fromIntegral wireId
          Just wireId → do
            modify $ IM.delete @Word32 $ fromIntegral wire0Id
            pure wireId
      HWPri nodeId →
        either (\Refl → primary =<< write @Pos nodeId) (\Refl → primary =<< write @Neg nodeId) $ decPolarity $ Proxy @a
  evalState IM.empty do
    for_ (V.zip auxs auxWires) \case
      (Left ext, Right int) → link ext =<< r' int
      (Right ext, Left int) → (`link` ext) =<< r' int
      _ → error "impossible"
    r' mainWire

eval :: Has Eval sig m => Node Neg → Node Pos → m ()
eval = curry \case
  (Era, b) → void $ travPorts (\(a :: WireEnd b) → case decPolarity $ Proxy @b of
      Left Refl → move Era a $> WireEnd 0
      Right Refl → move Nul a $> WireEnd 0
    ) b
  
  (Dup dupl dp1 dp2, Sup supl tm1 tm2)
    | dupl == supl → do
      link tm1 dp1
      link tm2 dp2
  (Dup dupl dp1 dp2, b) → runDup dupl dp1 dp2 $ travPorts dup b
  (a, Sup supl tm1 tm2) → runDup supl tm1 tm2 $ travPorts dup a
  
  (a, StaticHeavy heavyId auxs) → move a =<< instHeavy heavyId auxs

  (App arg ret, Lam var bod) → do
    link arg var
    link bod ret
  (App arg ret, Nul) → move Era arg *> move Nul ret
  (App {}, _) → wrong

  (Op2 op ret other, Word32 w) → move (Op1 op ret w) other
  (Op2 _ ret other, Nul) → move Nul ret *> move Era other
  (Op2 {}, _) → wrong

  (Op1 op ret w1, Word32 w2) →
    let op' = case op of
          P.Add → (+)
          P.Sub → (-)
          P.Mul → (*)
          P.Div → div
    in move (Word32 $ op' w1 w2) ret
  (Op1 _ ret _, Nul) → move Nul ret
  (Op1 {}, _) → wrong

  (Debug, Word32 x) → do
    sendIO $ print x
    pure ()
  (Debug, _) → wrong
  where wrong = error "wrong interaction"

newtype FreeVars = FreeVars {unFreeVars ∷ HashMap P.Ident (NonEmpty (WireEnd Pos))}

instance Semigroup FreeVars where
  FreeVars a <> FreeVars b = FreeVars $ HM.unionWith (<>) a b

instance Monoid FreeVars where
  mempty = FreeVars mempty

catchFree ∷ (Has (Writer FreeVars) sig m) ⇒ P.Ident → m a → m ([WireEnd Pos], a)
catchFree name act =
  censor @FreeVars (FreeVars . HM.delete name . unFreeVars) $
    (bimap (maybe [] toList . HM.lookup name . unFreeVars) id)
      <$> listen @FreeVars act

shareBetween ∷ (Has Eval sig m) ⇒ [WireEnd Pos] → m (WireEnd Pos)
shareBetween = \case
  [] → primary Era
  [x] → pure x
  x:xs@(_:_) → do
    f ← fresh -- TODO: use separate fresh
    primary . Dup (fromIntegral f) x =<< shareBetween xs

isAffine :: [a] → Bool
isAffine = \case
  [] → True
  [_] → True
  _:_:_ → False

-- Doesn't contract wires so is not performant at all.
isPrimary :: Has Eval sig m ⇒ WireEnd a → m Bool
isPrimary (WireEnd wire0Id) = do
  wire ← IM.lookup @(Either Word32 AnyNode) (fromIntegral wire0Id) <$> get
  case wire of
    Just (Left x) → isPrimary $ WireEnd $ fromIntegral x
    Just (Right _) → pure True
    Nothing → pure False

whilePop :: forall a sig m. Has (State (Seq a)) sig m ⇒ (a → m ()) → m ()
whilePop f = get @(Seq a) >>= \case
  (a :<| as) → put as *> f a *> whilePop f
  _ → pure ()

-- TODO: contract & retartget auxsList
-- deferred?
mkHeavy :: forall sig m. Has Eval sig m ⇒ WireEnd Neg → Vector AnyWireEnd → m StaticHeavyPackage
mkHeavy = \main0 auxs0 → do
  (pkg, (ma, au)) ← runWriter @(RevList AnyNode) (curry pure) $ evalState @Word32 0 $ evalState @(Seq AnyNode) mempty do
    m ← hdlPort' main0
    a ← for auxs0 $ either (fmap Left . hdlPort') (fmap Right . hdlPort')
    whilePop hdlNode
    pure (m, a)
  pure $ StaticHeavyPackage (V.length au) False ma au $ fromList $ toList pkg
  where
  -- auxsLen = length auxsList
  hdlNode :: forall sig2 m2. Has (Eval :+: State Word32 :+: State (Seq AnyNode) :+: Writer (RevList AnyNode)) sig2 m2 ⇒ AnyNode → m2 ()
  hdlNode origN = do
    n ← either (fmap Left . travPorts hdlPort) (fmap Right . travPorts hdlPort) origN
    tell @(RevList AnyNode) [n]
  hdlPort :: forall a sig2 m2. Has (Eval :+: State Word32 :+: State (Seq AnyNode)) sig2 m2 ⇒ DecPolarity a => WireEnd a -> m2 (WireEnd a)
  hdlPort = fmap packHV . hdlPort'
  hdlPort' :: forall a sig2 m2. Has (Eval :+: State Word32 :+: State (Seq AnyNode)) sig2 m2 ⇒ DecPolarity a => WireEnd a -> m2 (HeavyWireEnd a)
  hdlPort' wire0Id = do
    (wireId, thisM) ← contractWire wire0Id
    case thisM of
      Nothing → pure $ HWAux $ WireEnd wireId
      Just this → do
        modify @(Seq AnyNode) $ \q → q :|> either (\Refl → Right this) (\Refl → Left this) (decPolarity $ Proxy @a)
        state @Word32 \len → (len + 1, HWPri len)

{-

First of all, *I want Unicode*, but that's going to kill us I'm afraid.

Terms constructs of my abomination:
  forall X | T — impedicative quantification (`forall` from Fall From Grace)
  forall x : T | T' — type for erased lambdas.
  ** X : T | T' — type for dependent functions.
  \x y — a lambda
  \x A — a type for dependent function
-}


useFreeVar :: Has (Writer FreeVars :+: Eval) sig m ⇒ P.Ident → m (WireEnd Neg)
useFreeVar ident = do
  (n, p) ← newWire
  tell $ FreeVars $ HM.singleton ident (p :| [])
  pure n

-- censor + listen
intercept :: forall w m sig a. (Has (Writer w) sig m, Monoid w) => m a → m (w, a)
intercept = censor @w (const mempty) . listen @w

compile :: Has (Writer FreeVars :+: Eval) sig m => P.TermT → m (WireEnd Neg)
compile = \case
  -- P.Node captures pos val → do
  --   (freesInBod, val') ← intercept @FreeVars $ compile val
  --   -- Just compile into a heavy package, failing if free vars mismatch.
  --   -- The resulting heavy package
  --   undefined
  P.Let ((name, _, val) :| defs) bod → do
    (occInBod, bod') ← catchFree name $ compile case defs of
      [] → bod
      d:ds → P.Let (d :| ds) bod
    case occInBod of
      [] → pure ()
      _ → do
        (freesInVal, val') ← intercept @FreeVars $ compile val
        val'' ← runEmpty
          do -- fallback
            tell freesInVal
            pure val'
          pure
          do
            E.guard $ sum (length <$> unFreeVars freesInVal) <= 8 -- Cannot package when >8 auxs.
            E.guard =<< isPrimary val'
            let auxs = toList (unFreeVars freesInVal) >>= \(n, l) → (n,) <$> toList l
            for_ auxs \(_, aux) → E.guard . not =<< isPrimary aux
            -- Wrap
            heavyPackage ← mkHeavy val' (fromList $ Right . snd <$> auxs)
            heavyId ← fresh
            modify $ IM.insert heavyId heavyPackage

            primary =<< StaticHeavy (HeavyId $ fromIntegral heavyId) . fromList <$> for auxs \(i, _) → Left <$> useFreeVar i
        link val'' =<< shareBetween occInBod
    pure bod'
  P.Lam arg bod → do
    (occ, bod') ← catchFree arg $ compile bod
    occ' ← shareBetween occ
    primary $ Lam occ' bod'
  P.Op a op b → do
    a' ← compile a
    b' ← compile b
    (retn, retp) ← newWire
    move (Op2 op retp b') a'
    pure retn
  P.App f x → do
    f' ← compile f
    x' ← compile x
    (retn, retp) ← newWire
    move (App x' retp) f'
    pure retn
  P.NatLit x → primary $ Word32 x
  P.Var ident → useFreeVar ident

data Sizing a = SizeNul | SizeInline !Word32 | Size !a
  deriving Functor

-- | Returns total size in dwords and amount of data slots.
sizing :: Node a → Sizing (Word8, Word8)
sizing = \case
  App {} → j 2 0
  Lam {} → j 2 0
  Dup {} → j 2 0
  Sup {} → j 2 0
  Word32 l → SizeInline l
  Op2 {} → j 2 0
  Op1 {} → j 2 1
  Era → SizeNul
  Nul → SizeNul
  StaticHeavy _ auxs → Size (fromIntegral $ V.length auxs + 1, 1)
  Debug → SizeNul
  where j a b = Size (a, b)

packW16 :: (Word8, Word8) → Int
packW16 (a, b) = (fromIntegral a `unsafeShiftL` 8) .|. fromIntegral b

unpackW16 :: Int → (Word8, Word8)
unpackW16 x = (fromIntegral $ x `unsafeShiftR` 8, fromIntegral x)

-- | Returns subpacks and position of each input node in the respective subpack.
serPartitionSubpacks :: Vector AnyNode → (IntMap (Word32, RevList AnyNode), Vector Word32)
serPartitionSubpacks nodes = runIdentity $ runState @(IntMap (Word32, RevList AnyNode)) (curry pure) mempty $
  for nodes \node → either sizing sizing node & \case
    Size s →
      state @(IntMap (Word32, RevList AnyNode)) \subpacks →
        let
          subpackId = packW16 s
          (oldSize, oldMembers) = fromMaybe (0, []) $ IM.lookup subpackId subpacks
        in (IM.insert subpackId (oldSize + 1, oldMembers `revSnoc` node) subpacks, oldSize)
    _ → pure 0

-- | Returns packs (each containing subpacks) and position of each input node.
serPartitionPacks :: Vector AnyNode → (IntMap (Word32, RevList (Word8, Word32, RevList AnyNode)), Word32 → Sizing (Word8, Word32))
serPartitionPacks nodes =
  let
    (subpacks, nodeOffsetInSubpack) = serPartitionSubpacks nodes
    (packs, subpackOffsetInPack) = runIdentity $ runState (curry pure) mempty $ flip IM.traverseWithKey subpacks \(unpackW16 -> (packId, datas)) (size, subpack) →
      state @(IntMap (Word32, RevList (Word8, Word32, RevList AnyNode))) \oldPacks →
        let (oldPackSize, oldPackSubpacks) = fromMaybe (0, mempty) $ IM.lookup (fromIntegral packId) oldPacks
        in (IM.insert (fromIntegral packId) (oldPackSize + size, oldPackSubpacks `revSnoc` (datas, size, subpack)) oldPacks, oldPackSize)
  in (packs, \nodeId →
    either sizing sizing (P.fromJust (nodes V.!? fromIntegral nodeId))
    <&> \(packId, subpackId) → (packId, P.fromJust (IM.lookup (fromIntegral $ packW16 (packId, subpackId)) subpackOffsetInPack)
      + P.fromJust (nodeOffsetInSubpack V.!? fromIntegral nodeId)))

type HeavySerM = StateC Word32 (StateC (RevList (Word32, HeavyId)) (LiftC PutM))

serW32 :: Word32 → HeavySerM ()
serW32 x = do
  modify @Word32 (+1)
  sendM $ putWord32be x

serW64 :: Word64 → HeavySerM ()
serW64 x = do
  modify @Word32 (+2)
  sendM $ putWord64be x

serTravSlots_ :: forall f a. Applicative f ⇒ (Word8 → Either AnyHeavyWireEnd (HeavySerM ()) → f ()) → Node a → f ()
serTravSlots_ f = \case
  App a b → p 0 a *> p 1 b
  Lam a b → p 0 a *> p 1 b
  Dup _ a b → p 0 a *> p 1 b
  Sup _ a b → p 0 a *> p 1 b
  Word32 _ → pure ()
  Op2 _ a b → p 0 a *> p 1 b
  Op1 _ a b → p 0 a *> f 1 (Right $ serW64 $ fromIntegral b)
  Era → pure ()
  Nul → pure ()
  StaticHeavy heavyId b → sequenceA_ (zipWith (\i → either (p i) (p i)) [0..] $ toList b)
    *> f (fromIntegral $ V.length b) (Right do
      pos ← get @Word32
      modify $ (`revSnoc` (pos, heavyId))
      serW64 0)
  Debug → pure ()
  where
  p :: forall b. DecPolarity b => Word8 → WireEnd b → f ()
  p i = f i . Left . either (\Refl → Left . unpackHV) (\Refl → Right . unpackHV) (decPolarity (Proxy @b))

serHdlWires :: Vector AnyNode → IntMap (Word32, Word8)
serHdlWires = \nodes → runIdentity $ execWriter $ flip V.imapM_ nodes \nodeId →
  let
    f :: Node a → WriterC (IntMap (Word32, Word8)) Identity ()
    f = serTravSlots_ \portId → \case
      Left (Right (HWAux (WireEnd wire))) →
        tell $ IM.singleton (fromIntegral wire) (fromIntegral nodeId :: Word32, portId)
      _ → pure ()
  in either f f

packMeta :: Word8 → Word32 → Word32
packMeta a b = (fromIntegral a `unsafeShiftL` 24) .|. b

serMeta :: Node a → Word32
serMeta = uncurry packMeta . \case
  App {} → (4, 0)
  Lam {} → (4, 0)
  Dup l _ _ → (5, l)
  Sup l _ _ → (5, l)
  Word32 _ → (6, 0)
  Op2 op _ _ → (7, serOp op)
  Op1 op _ _ → (8, serOp op)
  Era → (3, 0)
  Nul → (3, 0)
  StaticHeavy _ x → (10, fromIntegral $ V.length x)
  Debug → (100, 0)
  where
  serOp :: P.OpT → Word32
  serOp = \case
    P.Add → 0
    P.Sub → 1
    P.Mul → 2
    P.Div → 3

serHeavy :: StaticHeavyPackage → PutM (RevList (Word32, HeavyId))
serHeavy (StaticHeavyPackage _hpersAux _hspecRes hmain0 hauxs hnodes) = do
  let auxForWire = serHdlWires hnodes
  let (packs, nodeIdToPos) = serPartitionPacks hnodes
  let packToVirt = IM.fromList $ zip (IM.keys packs) [0..]
  let
    ((subst, res_val_size), res_val) = runPutMBuilder $ runM $ runState (curry pure) [] $ execState 0 do
      for_ packs \(packSize, _subpacks) → serW32 packSize
      let
        mkRef (a :: Word8) (b :: Word32) (c :: Word8) = (P.fromJust (IM.lookup (fromIntegral a) packToVirt) `unsafeShiftL` 29) .|. (b `unsafeShiftL` 3) .|. fromIntegral c
        varFor (wireId :: Word32) =
          let
            (ab, c) = P.fromJust $ IM.lookup (fromIntegral wireId) auxForWire
          in case nodeIdToPos ab of
            Size (a, b) → mkRef a b c
            _ → error "impossible"
        serPort :: forall a. DecPolarity a ⇒ HeavyWireEnd a → HeavySerM ()
        serPort = \case
            HWAux (WireEnd a) → either (\Refl → serW32 (packMeta 1 0) *> serW32 (varFor a)) (\Refl → serW32 (packMeta 2 0)) $ decPolarity $ Proxy @a
            HWPri nodeId → do
              serW32 $ either serMeta serMeta $ P.fromJust $ hnodes V.!? fromIntegral nodeId
              case nodeIdToPos nodeId of
                SizeNul → pure ()
                SizeInline x → serW32 x
                Size (a, b) → serW32 $ mkRef a b 0
      for_ packs \(_packSize, toList → subpacks) →
        for_ subpacks \(datas, num, toList → nodes) → do
          serW32 $ (fromIntegral datas `unsafeShiftL` 29) .|. num
          let f = serTravSlots_ \_ → \case
                Left x → either serPort serPort x
                Right x → x
          for_ nodes $ either f f
      serPort hmain0
      for_ hauxs $ either serPort serPort
  putWord32be res_val_size
  putWord32be $ fromIntegral $ foldr (\k acc → (acc `unsafeShiftL` 4) .|. k) 0 $ IM.keys packs
  putWord8 $ foldr (\k acc → (acc `unsafeShiftL` 1) .|. either (const 0) (const 1) k) 0 $ hauxs
  putWord8 $ fromIntegral $ IM.size packs
  putBuilder res_val
  pure subst

serHeavyRec :: StaticHeavyPackage → EvalC LByteString
serHeavyRec rootHeavy = fmap toLazyByteString $ evalState (S.empty @HeavyId) $ evalAccum (IM.empty @Word32) $ execWriter @Builder do
  let
    ser h = do
      let (UnsafeRevList subst, res) = runPutMBuilder $ serHeavy h
      tell res
      tell $ execPut $ putWord32be $ fromIntegral $ length subst -- sorry
      for_ subst \(pos, HeavyId heavyId) → do
        heavyIdToVirtId ← look
        virtId ← case IM.lookup (fromIntegral heavyId) heavyIdToVirtId of
          Nothing → do
            let v = fromIntegral $ IM.size heavyIdToVirtId
            add $ IM.singleton (fromIntegral heavyId) v
            modify $ (:|> HeavyId heavyId)
            pure v
          Just v → pure v
        tell $ execPut $ putWord32be pos *> putWord32be virtId
  ser rootHeavy
  whilePop \(HeavyId heavyId) → do
    heavy ← P.fromJust . IM.lookup (fromIntegral heavyId) <$> get
    ser heavy

type EvalC a = StateC (IntMap (Either Word32 AnyNode)) (StateC (IntMap StaticHeavyPackage) (FreshC IO)) a

runEvalC :: EvalC a → IO a
runEvalC = evalFresh 0 . evalState IM.empty . evalState IM.empty

compileFile :: FilePath → EvalC (WireEnd Neg)
compileFile fileName = do
  parsed ← either (error . show) pure =<< lift (sendIO $ P.parseFile fileName)
  runWriter @FreeVars
    (\(FreeVars frees) res → do
      unless (HM.null frees) $
        error $
          "Unknown identifiers: "
            <> intercalate ", " (show . P.pIdent . fst <$> toList frees)
      pure res
    )
    $ compile parsed

compileFileRun :: FilePath → EvalC ()
compileFileRun fileName = compileFile fileName >>= move Debug

compileFileToFile :: FilePath → IO ()
compileFileToFile file = runEvalC do
  pri ← compileFile (file <> ".fad") 
  root ← mkHeavy pri []
  fadobj ← serHeavyRec root
  writeFileBinary (file <> ".fadobj") $ toStrictBytes fadobj

main ∷ IO ()
main = pure ()
