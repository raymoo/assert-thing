module Main where

-- import Assert.Lang
import Assert.Lang.Parse
import Assert.SMT

import qualified Text.Trifecta as P

import System.Environment

main :: IO ()
main = do
  (fileName : _) <- getArgs
  mExpr <- P.parseFromFile programP fileName
  case mExpr of
    Nothing -> putStrLn "Parsing failed"
    Just expr -> do
      results <- checkExpr expr
      case results of
        Nothing -> putStrLn "All good!"
        Just assignments -> do
          putStrLn "Assertion can fail with assignments: "
          print assignments
