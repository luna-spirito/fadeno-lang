module Main where

import Data.ByteString.Lazy (ByteString)
import Data.List (sort)
import Prelude (IO, filter, map, return, (.), ($), (<$>), (==))
import System.Directory (listDirectory)
import System.FilePath
import System.OsPath (unsafeEncodeUtf)
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.Golden (goldenVsString)
import Test.Tasty.HUnit (testCase)
import Driver (testBuild)

fadSourceDir :: FilePath
fadSourceDir = "fad/test"

goldenDir :: FilePath
goldenDir = "test/golden"

mkGoldenTests :: IO TestTree
mkGoldenTests = do
  files <- sort . filter ((== ".fad") . takeExtension) <$> listDirectory fadSourceDir
  return $ testGroup "golden build" $ map mkGoldenTest files

mkGoldenTest :: FilePath -> TestTree
mkGoldenTest fadFile =
  goldenVsString
    testName
    goldenPath
    action
  where
    testName = dropExtension fadFile
    goldenPath = goldenDir </> replaceExtension fadFile ".golden"
    action :: IO ByteString
    action = testBuild (unsafeEncodeUtf $ fadSourceDir </> dropExtension fadFile)

smokeTest :: TestTree
smokeTest = testCase "fadeno-lang runs" $ return ()

main :: IO ()
main = do
  goldenTests <- mkGoldenTests
  defaultMain $ testGroup "fadeno" [goldenTests, smokeTest]
