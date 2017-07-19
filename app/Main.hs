module Main where

-- import Assert.Lang
import Assert.Lang.Parse
import Assert.SMT

import SimpleSMT (Value)

import Text.PrettyPrint.ANSI.Leijen (pretty, putDoc)

import Text.Trifecta (Caret)
import qualified Text.Trifecta as P

import Data.Foldable (traverse_)
import System.Environment

main :: IO ()
main = do
  (fileName : _) <- getArgs
  mExpr <- P.parseFromFile programP fileName
  case mExpr of
    Nothing -> putStrLn "Parsing failed"
    Just expr -> do
      failures <- checkExpr expr
      traverse_ printFailure failures
      if null failures then putStrLn "All good" else pure ()

printFailure :: ([(String, Value)], Caret) -> IO ()
printFailure (assgns, location) = do
  putStrLn "\nFailed assertion:"
  putDoc . pretty . P.render $ location
  putStrLn ""
  putStrLn "Assertion can fail with assignments: "
  print assgns
