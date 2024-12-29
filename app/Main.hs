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
import Data.List (uncons)
import GHC.Exts (IsList (..))
import Parser qualified as P
import RIO hiding (link, ask, runReader, toList)
import RIO.HashMap qualified as HM
import qualified Data.IntMap as IM
import qualified RIO.Partial as P
import Control.Carrier.Reader (ReaderC, runReader)
import Control.Effect.Reader (ask)
import Control.Algebra
import Control.Carrier.Empty.Church (runEmpty)
import qualified Control.Effect.Empty as E
import Type.Reflection ((:~:) (..))
import qualified RIO.Vector as V
import Control.Effect.Lift (Lift, sendIO)
import Control.Carrier.Fresh.Church (FreshC, evalFresh)
import Control.Carrier.Error.Church (runError)
import Control.Effect.Throw (throwError)
import Control.Carrier.Writer.Church (runWriter, execWriter)
import RIO.Text (intercalate)
import RIO.Seq  (Seq(..))
import Data.Bits (unsafeShiftL, (.|.), unsafeShiftR, (.&.))

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

newtype RevList a = UnsafeRevList [a] deriving (Functor)

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
  StaticHeavy :: !Word32 → !(Vector AnyWireEnd) → Node Pos
  Debug :: Node Neg

type AnyNode = Either (Node Neg) (Node Pos)

-- Format of heavy package differs between -lang and -jit.
data StaticHeavyPackage = StaticHeavyPackage !Int !Bool !(Vector AnyNode)

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

-- | Extension over WireEnd that also allows to serialise wires to primary ports;
-- wires to heavy's auxiliary ports, both persistent and temporary (the ones used for multi-operand nodes introduced by -op1-op2+>).
data HeavyWireEnd (pol :: Polarity)
  = HWInternalAux !(WireEnd pol)
  | HWInternalPri !Word32
  | HWPersistentAux !Word32
  | HWTemporaryAux !Word32

packHV :: HeavyWireEnd a → WireEnd a
packHV hv =
  let (tag, val) = case hv of
        HWInternalAux (WireEnd v) → (0, v)
        HWInternalPri v → (1, v)
        HWPersistentAux v → (2, v)
        HWTemporaryAux v → (3, v)
  in WireEnd $ (tag `unsafeShiftL` 30) .|. val

unpackHV :: WireEnd a → HeavyWireEnd a
unpackHV (WireEnd x) =
  let (tag, val) = (x `unsafeShiftR` 30, x .&. 0x3FFFFFFF)
  in case tag of
    0 → HWInternalAux $ WireEnd val
    1 → HWInternalPri val
    2 → HWPersistentAux val
    4 → HWTemporaryAux val
    _ → error "unknown tag"

instHeavy :: forall sig m. Has Eval sig m => Word32 → Vector AnyWireEnd → m (Node Pos)
instHeavy heavyId auxs = do
  StaticHeavyPackage persAuxsLen hasResAux ns ← P.fromJust . IM.lookup @StaticHeavyPackage (fromIntegral heavyId) <$> get
  let
    write :: forall a. DecPolarity a => Word32 → StateC (IntMap Word32) m (Node a)
    write i = case (decPolarity $ Proxy @a, P.fromJust $ ns V.!? fromIntegral i) of
      (Left Refl, Left n) → travPorts r n--case n of
      (Right Refl, Right n) → travPorts r n--case n of
      _ → error "impossible"
    
    r :: forall a. DecPolarity a ⇒ WireEnd a → StateC (IntMap Word32) m (WireEnd a)
    r hw0 = case unpackHV hw0 of
      HWInternalAux (WireEnd wire0Id) → do
        wireIdM ← IM.lookup (fromIntegral wire0Id) <$> get
        WireEnd <$> case wireIdM of
          Nothing → do
            wireId ← fresh
            modify $ IM.insert @Word32 (fromIntegral wire0Id) $ fromIntegral wireId
            pure $ fromIntegral wireId
          Just wireId → do
            modify $ IM.delete @Word32 $ fromIntegral wire0Id
            pure wireId
      HWInternalPri nodeId →
        either (\Refl → primary =<< write @Pos nodeId) (\Refl → primary =<< write @Neg nodeId) $ decPolarity $ Proxy @a
      HWPersistentAux wireId → pure case (decPolarity $ Proxy @a, P.fromJust $ auxs V.!? fromIntegral wireId) of
        (Left Refl, Left a) → a
        (Right Refl, Right a) → a
        _ → error "impossible"
  evalState IM.empty $ write 0

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
  
  (a, StaticHeavy heavyId auxs) → eval a =<< instHeavy heavyId auxs

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

-- TODO: contract & retartget auxsList
-- deferred?
mkHeavy :: forall sig m. Has Eval sig m ⇒ [WireEnd Pos] → WireEnd Neg → m StaticHeavyPackage
mkHeavy auxsList = \main0 → do
    for_ (zip [0..] auxsList) \(i, wire0Id) → do
      (wireId, _) ← contractWire wire0Id
      modify $ IM.insert @(Either Word32 AnyNode) (fromIntegral wireId) $ Left $ (\(WireEnd a) → a) $ packHV $ HWPersistentAux i
    res ← execWriter @(RevList AnyNode) $ evalState @Word32 0 $ evalState @(Seq AnyNode) mempty do
      _ ← hdlPort main0
      whilePop hdlNode
    let resVec = fromList $ toList res
    -- TODO: customs...
    pure $ StaticHeavyPackage (V.length resVec) False resVec
  where
  -- auxsLen = length auxsList
  whilePop :: forall sig2 m2. Has (State (Seq AnyNode)) sig2 m2 ⇒ (AnyNode → m2 ()) → m2 ()
  whilePop f = get @(Seq AnyNode) >>= \case
    (a :<| as) → put as *> f a *> whilePop f
    _ → pure ()
  hdlNode :: forall sig2 m2. Has (Eval :+: State Word32 :+: State (Seq AnyNode) :+: Writer (RevList AnyNode)) sig2 m2 ⇒ AnyNode → m2 ()
  hdlNode origN = do
    n ← either (fmap Left . travPorts hdlPort) (fmap Right . travPorts hdlPort) origN
    tell @(RevList AnyNode) [n]
  hdlPort :: forall a sig2 m2. Has (Eval :+: State Word32 :+: State (Seq AnyNode)) sig2 m2 ⇒ DecPolarity a => WireEnd a -> m2 (WireEnd a)
  hdlPort wire0Id = do
    (wireId, thisM) ← contractWire wire0Id
    case thisM of
      Nothing → pure $ WireEnd wireId
      Just this → do
        modify @(Seq AnyNode) $ \q → q :|> either (\Refl → Right this) (\Refl → Left this) (decPolarity $ Proxy @a)
        state @Word32 \len → (len + 1, packHV $ HWInternalPri len)

useFreeVar :: Has (Writer FreeVars :+: Eval) sig m ⇒ P.Ident → m (WireEnd Neg)
useFreeVar ident = do
  (n, p) ← newWire
  tell $ FreeVars $ HM.singleton ident (p :| [])
  pure n

-- censor + listen
intercept :: forall w m sig a. (Has (Writer w) sig m, Monoid w) => m a → m (w, a)
intercept = censor @w (const mempty) . listen @w

compile :: Has (Writer FreeVars :+: Eval) sig m => P.ExprT → m (WireEnd Neg)
compile = \case
  P.Node captures pos val → do
    (freesInBod, val') ← intercept @FreeVars $ compile val
    -- Just compile into a heavy package, failing if free vars mismatch.
    -- The resulting heavy package
    undefined
  P.Let ((name, val) :| defs) bod → do
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
            heavyPackage ← mkHeavy (snd <$> auxs) val'
            heavyId ← fresh
            modify $ IM.insert heavyId heavyPackage

            primary =<< StaticHeavy (fromIntegral heavyId) . fromList <$> for auxs \(i, _) → Left <$> useFreeVar i
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
  P.Nat x → primary $ Word32 x
  P.Var ident → useFreeVar ident
            
{-
serOp ∷ Putter P.OpT
serOp =
  putWord8 . \case
    P.Add → 0
    P.Sub → 1
    P.Mul → 2
    P.Div → 3

serNode ∷ Putter (Port pol)
serNode port =
  let
    (tag, val) = case port of
      FreeN x → (0, putWord32be $ fromIntegral x)
      FreeP x → (0, putWord32be $ fromIntegral x)
      App a b → (1, serNode a *> serNode b)
      Lam a b → (1, serNode a *> serNode b)
      Dup l a b → (2, putWord32be l *> serNode a *> serNode b)
      Sup l a b → (2, putWord32be l *> serNode a *> serNode b)
      Word32 w → (3, putWord32be w)
      Op2 op a b → (4, serOp op *> serNode a *> serNode b)
      Era → (5, pure ())
      Nul → (5, pure ())
      -- Chu a b c d → (6, serNode a *> serNode b *> serNode c *> serNode d)
   in
    putWord8 tag *> val

serNet ∷ Putter (Port Pos, [(Port Neg, Port Pos)])
serNet (a, b) = serNode a *> for_ b \(c, d) → serNode c *> serNode d
-}

-- debugShow :: (Port Pos, [(Port Neg, Port Pos)])
-- debugShow (a, b)
-- prettyNode :: Node pol -> Doc AnsiStyle
-- prettyNode port =
--   let (tag :: Doc AnsiStyle, sub :: [Doc AnsiStyle]) = case port of
--         App a b → ("App", [prettyNode a, prettyNode b])
--         Lam a b → ("Lam", [prettyNode a, prettyNode b])
--         Dup l a b → ("Dup " <> pretty l, [prettyNode a, prettyNode b])
--         Sup l a b → ("Sup " <> pretty l, [prettyNode a, prettyNode b])
--         Word32 b → ("Word32" <+> pretty b, [])
--         Op2 op a b → ("Op2" <+> P.pOp op, [prettyNode a, prettyNode b])
--         Era → ("Era", [])
--         Nul → ("Nul", [])
--         -- Chu _ _ _ _ → undefined
--         -- FreeN x → ("FreeN" <+> pretty x, [])
--         -- FreeP x → ("FreeP" <+> pretty x, [])
--   in tag <> if null sub then mempty else nest 1 (line <> vsep sub)

-- debugRun :: 

-- printNet :: (Node Pos, [(Node Neg, Node Pos)]) → IO ()
-- printNet (a, b) = renderIO stdout $ layoutSmart defaultLayoutOptions $
--   let entries = prettyNode a : (b <&> \(c, d) -> vsep [prettyNode c, "~", prettyNode d])
--   in concatWith (\x y → x <> "\n----\n" <> y) entries <> line
-- debugReadInt → 

type EvalC a = StateC (IntMap (Either Word32 AnyNode)) (StateC (IntMap StaticHeavyPackage) (FreshC IO)) a

runEvalC :: EvalC a → IO a
runEvalC = evalFresh 0 . evalState IM.empty . evalState IM.empty

compileFile :: FilePath → EvalC (Either Text (WireEnd Neg))
compileFile fileName = runError (pure . Left) (pure . Right) do
  parsed ← either throwError pure =<< lift (sendIO $ P.parseFile fileName)
  runWriter @FreeVars
    (\(FreeVars frees) res → do
      unless (HM.null frees) $
        throwError $
          "Unknown identifiers: "
            <> intercalate ", " (decodeUtf8Lenient . P.unIdent . fst <$> toList frees)
      pure res
    )
    $ compile parsed

compileFileRun :: FilePath → EvalC (Either Text ())
compileFileRun fileName = compileFile fileName >>= either (pure . Left) \res →
  move Debug res $> Right ()

-- compileFileToFile :: FilePath → IO (Either Text ())
-- compileFileToFile file = compileFile (file <> ".fad") >>= traverse (writeFileBinary (file <> ".fadobj") . runPut . serNet)

main ∷ IO ()
main = pure ()
