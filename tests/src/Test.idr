module Test

import Data.List
import System

import RandomTest
import Control.Monad.Error.Either

%default partial

run_test : String -> EitherT String IO () -> IO Bool
run_test name test = do
  Right () <- runEitherT test
  | Left err => putStrLn "\{name}: failed \{err}" $> False
  putStrLn "\{name}: success" $> True

run : List (IO Bool) -> IO ()
run tests = do
  results <- sequence tests
  let [] = filter not results
  | xs => putStrLn "\{show (length xs)} tests failed" *> exitFailure
  putStrLn "all tests passed"

export
main : IO ()
main = run [ (run_test "csprng" test_random) ]
