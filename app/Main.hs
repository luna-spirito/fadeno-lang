{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

module Main where

import Control.Carrier.Error.Church (runError, throwError)
import Control.Carrier.Fresh.Church (FreshC, evalFresh)
import Control.Carrier.State.Church
import Control.Carrier.Writer.Church (WriterC, runWriter)
import Control.Effect.Fresh (fresh)
import Control.Effect.Writer (Writer, censor, listen, tell)
import Data.Kind (Type)
import Data.List (uncons)
import Data.Serialize (Putter, putWord32be, putWord8, runPut)
import GHC.Exts (IsList (..))
import Parser qualified as P
import RIO
import RIO.HashMap qualified as HM
import RIO.Text (intercalate)

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

data Port ∷ Polarity → Type where
  App ∷ Port Pos → Port Neg → Port Neg
  Lam ∷ Port Neg → Port Pos → Port Pos
  Dup ∷ Port Neg → Port Neg → Port Neg
  Sup ∷ Port Pos → Port Pos → Port Pos
  W32 ∷ Word32 → Port Pos
  Op2 ∷ P.OpT → Port Pos → Port Neg → Port Neg
  -- Op1 :: P.OpT → Port Pos → Port Neg → Port Neg
  Era ∷ Port Neg
  Nul ∷ Port Pos
  Chu ∷ Port Pos {- nil -} → Port Neg {- cons arg -} → Port Pos {- cons ret -} → Port Neg {- ret -} → Port Neg
  FreeN ∷ Int → Port Neg
  FreeP ∷ Int → Port Pos

newtype FreeVars = FreeVars {unFreeVars ∷ HashMap P.Ident (NonEmpty Int)}

instance Semigroup FreeVars where
  FreeVars a <> FreeVars b = FreeVars $ HM.unionWith (<>) a b

instance Monoid FreeVars where
  mempty = FreeVars mempty

catchFree ∷ (Has (Writer FreeVars) sig m) ⇒ P.Ident → m a → m (Maybe (NonEmpty Int), a)
catchFree name act =
  censor @FreeVars (FreeVars . HM.delete name . unFreeVars) $
    (bimap (HM.lookup name . unFreeVars) id)
      <$> listen @FreeVars act

shareBetween ∷ NonEmpty Int → Port Neg
shareBetween = \case
  x :| [] → FreeN x
  x :| (y : xs) → Dup (FreeN x) (shareBetween $ y :| xs)

-- TODO: better balancing?

compilePort ∷ P.ExprT → WriterC FreeVars (WriterC (RevList (Port Neg, Port Pos)) (FreshC Identity)) (Port Pos)
compilePort = \case
  P.Lam arg bod → do
    (occ, bod') ← catchFree arg $ compilePort bod
    pure $ case occ of
      Nothing → Lam Era bod'
      Just occ' → Lam (shareBetween occ') bod'
  P.Let [] res → compilePort res
  P.Let ((name, val) : xs) res → do
    (occ, bod') ← catchFree name $ compilePort $ P.Let xs res
    case occ of
      Nothing → pure ()
      Just occ' → do
        val' ← compilePort val
        tell @(RevList _) [(shareBetween occ', val')]
    pure bod'
  P.Op a op b → do
    a' ← compilePort a
    b' ← compilePort b
    retwire ← fresh
    tell @(RevList _) [(Op2 op b' (FreeN retwire), a')]
    pure $ FreeP retwire
  P.App f x → do
    f' ← compilePort f
    x' ← compilePort x
    retwire ← fresh
    tell @(RevList _) [(App x' (FreeN retwire), f')]
    pure $ FreeP retwire
  P.Nat x → pure $ W32 x
  P.Var x → do
    wire ← fresh
    tell $ FreeVars $ HM.singleton x $ wire :| []
    pure $ FreeP wire
  P.BuiltinsChurch → do
    nil ← fresh
    consArg ← fresh
    consRet ← fresh
    ret ← fresh
    pure $
      Lam
        (FreeN nil)
        ( Lam
            (App (FreeP consArg) (FreeN consRet))
            ( Lam
                (Chu (FreeP nil) (FreeN consArg) (FreeP consRet) (FreeN ret))
                (FreeP ret)
            )
        )

-- TODO: perform duplications inside of lambdas/ifs and not outside.

-- This is very lazy and non-performant.
connect ∷ RevList (Port Neg, Port Pos) → Port Pos → (Port Pos, [(Port Neg, Port Pos)])
connect (UnsafeRevList connections) =
  let
    (redexes, (HM.fromList → subNeg, HM.fromList → subPos)) =
      partitionEithers
        <$> partitionEithers
          ( connections <&> \case
              (FreeN x, FreeP y) → Right $ Left (x, FreeP y)
              (FreeN x, y) → Right $ Left (x, y)
              (x, FreeP y) → Right $ Right (y, x)
              (x, y) → Left (x, y)
          )
    neg ∷ Port Neg → Port Neg
    neg = \case
      App a b → App (pos a) (neg b)
      Dup a b → Dup (neg a) (neg b)
      Op2 op a b → Op2 op (pos a) (neg b)
      Era → Era
      Chu a b c d → Chu (pos a) (neg b) (pos c) (neg d)
      FreeN x → case HM.lookup x subPos of
        Just y → y
        Nothing → FreeN x
    pos ∷ Port Pos → Port Pos
    pos = \case
      Lam a b → Lam (neg a) (pos b)
      Sup a b → Sup (pos a) (pos b)
      W32 a → W32 a
      Nul → Nul
      FreeP x → case HM.lookup x subNeg of
        Just y → y
        Nothing → FreeP x
   in
    \root → (pos root, redexes)

compile ∷ P.ExprT → Either [P.Ident] (Port Pos, [(Port Neg, Port Pos)])
compile expr =
  let (lateConnections, (FreeVars frees, root)) = runIdentity $ evalFresh 0 $ runWriter (curry pure) $ runWriter (curry pure) $ compilePort expr
   in case frees of
        [] → Right $ connect lateConnections root
        xs → Left (HM.keys xs)

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
      App a b → (1, serNode a *> serNode b)
      Lam a b → (1, serNode a *> serNode b)
      Dup a b → (2, serNode a *> serNode b)
      Sup a b → (2, serNode a *> serNode b)
      W32 w → (3, putWord32be w)
      Op2 op a b → (4, serOp op *> serNode a *> serNode b)
      Era → (5, pure ())
      Nul → (5, pure ())
      Chu a b c d → (6, serNode a *> serNode b *> serNode c *> serNode d)
      FreeN x → (6, putWord32be $ fromIntegral x)
      FreeP x → (6, putWord32be $ fromIntegral x)
   in
    putWord8 tag *> val

serNet ∷ Putter (Port Pos, [(Port Neg, Port Pos)])
serNet (a, b) = serNode a *> for_ b \(c, d) → serNode c *> serNode d

compileFile ∷ FilePath → IO (Either Text ())
compileFile file = runError (pure . Left) (pure . Right) do
  let orDie = either throwError pure
  parsed ← orDie =<< lift (P.parseFile $ file <> ".fad")
  compiled ←
    orDie
      $ mapLeft
        ( \ids →
            "Unknown identifiers: "
              <> intercalate ", " (decodeUtf8Lenient . P.unIdent <$> ids)
        )
      $ compile parsed
  writeFileBinary (file <> ".fadobj") $ runPut $ serNet compiled

main ∷ IO ()
main = pure ()
