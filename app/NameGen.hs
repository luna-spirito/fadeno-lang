{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use const" #-}
module NameGen where

import Control.Algebra
import Control.Effect.State (State, state)
import Data.ByteString qualified as B
import Data.Char (ord)
import Data.Foldable (minimum, minimumBy)
import Data.RRBVector
import RIO hiding (Vector, zip, zipWith)

newtype Name = Name ByteString deriving (Show)

letters ∷ Vector Word8
letters = fromIntegral . ord <$> "abcdefghijklmnoprstuvz"

vowels, consonants, voiced, unvoiced ∷ Vector Word8
vowels = fromIntegral . ord <$> "aeiou"
consonants = fromIntegral . ord <$> "bcdfghjklmnprstvz"
voiced = fromIntegral . ord <$> "bdgjlmnrtvzc"
unvoiced = fromIntegral . ord <$> "fhkps"

-- TODO: better pattern-matching-system? I don't know.
allowed ∷ Maybe Word8 → Maybe Word8 → Word8 → Bool
allowed aM bM c =
  case bM of
    Nothing → True
    Just b →
      c
        /= b
        && not (b `elem` voiced && c `elem` consonants)
        && not (b `elem` unvoiced && c `elem` voiced)
        && case aM of
          Nothing → True
          Just a →
            not (a `elem` vowels && b `elem` vowels && c `elem` vowels)
              && not (a `elem` consonants && b `elem` consonants && c `elem` consonants)

newtype UsedNames = UsedName (Vector (Int, Maybe UsedNames)) deriving (Show)
emptyTaken ∷ Vector (Int, Maybe UsedNames)
emptyTaken = (\_ → (0, Nothing)) <$> letters
instance Semigroup UsedNames where
  UsedName x <> UsedName y =
    UsedName
      $ zipWith
        ( \(aCnt, a) (bCnt, b) →
            ( aCnt + bCnt
            , case (a, b) of
                (Nothing, Nothing) → Nothing
                _ → Just $ fromMaybe mempty a <> fromMaybe mempty b
            )
        )
        x
        y
instance Monoid UsedNames where
  mempty = UsedName emptyTaken

mk ∷ ByteString → (Name, UsedNames)
mk = \x → (Name x, fromMaybe mempty $ buildFor Nothing Nothing $ B.unpack x)
 where
  buildFor ∷ Maybe Word8 → Maybe Word8 → [Word8] → Maybe UsedNames
  buildFor aM bM = \case
    [] → Just mempty
    (x : xs)
      | Just letterI ← findIndexL (== x) letters
      , allowed aM bM x →
          (\next → UsedName $ adjust' letterI (\_ → (1, Just next)) emptyTaken) <$> buildFor bM (Just x) xs
    _ → Nothing

gen ∷ UsedNames → (UsedNames, Name)
gen = second Name . go Nothing Nothing . Just
 where
  go ∷ Maybe Word8 → Maybe Word8 → Maybe UsedNames → (UsedNames, ByteString)
  go aM bM = \case
    Nothing → (UsedName emptyTaken, "")
    Just (UsedName taken) →
      let
        cmpLetters l r = case (allowed aM bM l, allowed aM bM r) of
          (False, _) → GT
          (_, False) → LT
          (True, True) → EQ
        ((bestI, bestLetter), (oldCnt, old)) =
          minimumBy (\((_, l), (u1, _)) ((_, r), (u2, _)) → cmpLetters l r <> compare u1 u2)
            $ zip (zip [0 .. length letters - 1] letters) taken
        (new, res0) = go bM (Just bestLetter) old
       in
        (UsedName $ adjust' bestI (\_ → (oldCnt + 1, Just new)) taken, bestLetter `B.cons` res0)

genM ∷ (Has (State UsedNames) sig m) ⇒ m Name
genM = state gen
