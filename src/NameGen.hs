{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use const" #-}
module NameGen where

import Data.ByteString qualified as B
import Data.Char (ord)
import Data.Foldable (minimumBy)
import Data.RRBVector
import RIO hiding (Vector, zip, zipWith)

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

newtype UsedNames = UsedNames (Vector (Int, Maybe UsedNames)) deriving (Show)

emptyUsedNames ∷ UsedNames
emptyUsedNames = UsedNames $ (\_ → (0, Nothing)) <$> letters

use ∷ ByteString → UsedNames → UsedNames
use = \i s → fromMaybe s $ go Nothing Nothing (Just s) (B.unpack i)
 where
  go ∷ Maybe Word8 → Maybe Word8 → Maybe UsedNames → [Word8] → Maybe UsedNames
  go aM bM oldM = \case
    [] → Just $ fromMaybe emptyUsedNames oldM
    (x : xs)
      | Just letterI ← findIndexL (== x) letters
      , allowed aM bM x →
          let
            (UsedNames old) = fromMaybe emptyUsedNames oldM
            (innerCnt0, inner0) = fromMaybe (error "Internal error: impossible") $ old !? letterI
           in
            (\inner → UsedNames $ adjust' letterI (\_ → (innerCnt0 + 1, Just inner)) old) <$> go bM (Just x) inner0 xs
    _ → Nothing

gen ∷ UsedNames → (UsedNames, ByteString)
gen = go Nothing Nothing . Just
 where
  go ∷ Maybe Word8 → Maybe Word8 → Maybe UsedNames → (UsedNames, ByteString)
  go aM bM = \case
    Nothing → (emptyUsedNames, "")
    Just (UsedNames taken) →
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
        (UsedNames $ adjust' bestI (\_ → (oldCnt + 1, Just new)) taken, bestLetter `B.cons` res0)
