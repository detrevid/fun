module Main where

import LexFun
import ParFun
import AbsFun
import Interpreter
import ErrM
import Debug.Trace

import Control.Monad (when)
import Data.Char
import Text.Read
import System.Exit (exitFailure)

doTest :: String -> IO Bool
doTest testName = do
  let inTestName  = testName ++ ".in"
      outTestName = testName ++ ".out"
  inT  <- readFile inTestName
  outT <- readFile outTestName
  let inTS = (iterpret $ inT) ++ "\n"
  return $ inTS == outT

iterpret :: String -> String
iterpret s =
  let p = pProgram (myLexer s)
  in case p of
    Ok prog -> show $ transProgram prog
    Bad m -> show m

testsPath = "examples/"
egPref = "eg"
goodTestsPath = testsPath ++ "good/"
badTestsPath = testsPath ++ "bad/"
goodTests = [ goodTestsPath ++ egPref ++ show n | n <- [1..30] ]
badTests = [ badTestsPath ++ egPref ++ show n | n <- [1..14] ]

main = do
  tests <- mapM doTest (goodTests ++ badTests)
  let evalTest (nr, ans) = if ans then trace ("Test " ++ show nr ++ ": OK") False
                                  else trace ("Test " ++ show nr ++ ": FAIL") True
  when (any evalTest (zip [1..] tests)) exitFailure
