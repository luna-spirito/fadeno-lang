module Main where

import Data.ByteString.Lazy (ByteString)
import Data.List (concat, isPrefixOf, sort)
import Prelude (Bool, FilePath, IO, filter, fmap, map, mapM, not, return, (.), ($), (&&), (++), (<$>), (==), (||))
import System.Directory (doesDirectoryExist, listDirectory)
import System.FilePath
import System.OsPath (unsafeEncodeUtf)
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.Golden (goldenVsString)
import Test.Tasty.HUnit (testCase)
import Driver (testBuild, testNormalize)

fadSourceDir :: FilePath
fadSourceDir = "fad"

goldenDir :: FilePath
goldenDir = "test/golden"

-- Recursively find all .fad files in a directory
findFadFiles :: FilePath -> IO [FilePath]
findFadFiles dir = do
  entries <- listDirectory dir
  fmap concat $ mapM (processEntry dir) entries
  where
    processEntry :: FilePath -> FilePath -> IO [FilePath]
    processEntry base entry = do
      let fullPath = base </> entry
      isDir <- doesDirectoryExist fullPath
      if isDir
        then findFadFiles fullPath
        else if takeExtension entry == ".fad"
          then return [fullPath]
          else return []

mkGoldenTests :: IO [TestTree]
mkGoldenTests = do
  allFiles <- sort <$> findFadFiles fadSourceDir
  let isNormTest path = ("fad/normtest/" `isPrefixOf` path) || ("fad\\normtest\\" `isPrefixOf` path)
      normFiles = filter isNormTest allFiles
      buildFiles = filter (not . isNormTest) allFiles
  let buildTests = testGroup "golden build" $ map mkGoldenTest buildFiles
      normTests = testGroup "normalization" $ map mkNormTest normFiles
  return [buildTests, normTests]

mkGoldenTest :: FilePath -> TestTree
mkGoldenTest fadFilePath =
  goldenVsString
    testName
    goldenPath
    action
  where
    testName = makeRelative fadSourceDir (dropExtension fadFilePath)
    -- Golden file path mirrors the source structure
    goldenPath = goldenDir </> makeRelative fadSourceDir (replaceExtension fadFilePath ".golden")
    action :: IO ByteString
    action = testBuild (unsafeEncodeUtf $ dropExtension fadFilePath)

mkNormTest :: FilePath -> TestTree
mkNormTest fadFilePath =
  goldenVsString
    testName
    goldenPath
    action
  where
    testName = makeRelative fadSourceDir (dropExtension fadFilePath)
    goldenPath = goldenDir </> makeRelative fadSourceDir (replaceExtension fadFilePath ".golden")
    action :: IO ByteString
    action = testNormalize (unsafeEncodeUtf $ dropExtension fadFilePath)

smokeTest :: TestTree
smokeTest = testCase "fadeno-lang runs" $ return ()

main :: IO ()
main = do
  goldenTests <- mkGoldenTests
  defaultMain $ testGroup "fadeno" (goldenTests ++ [smokeTest])
