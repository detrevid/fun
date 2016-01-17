module Main where

import Fun.BNFC.AbsFun
import Fun.BNFC.ErrM
import Fun.BNFC.LexFun
import Fun.BNFC.ParFun
import Fun.Interpreter

import Control.Monad (when)
import Data.Char
import Debug.Trace
import Text.Read
import System.Exit (exitFailure)

doTest :: String -> IO Bool
doTest testName = do
  let inTestName  = testName ++ ".in"
      outTestName = testName ++ ".out"
  inT  <- readFile inTestName
  outT <- readFile outTestName
  let inTS = (interpret $ inT) ++ "\n"
  return $ inTS == outT

interpret :: String -> String
interpret s =
  let p = pProgram (myLexer s)
  in case p of
    Ok prog -> show $ transProgram prog
    Bad m -> show m

testsPath = "examples/"
egPref = "eg"
goodTestsPath = testsPath ++ "good/"
badTestsPath = testsPath ++ "bad/"
goodTests = [ goodTestsPath ++ egPref ++ show n | n <- [1..31] ]
badTests = [ badTestsPath ++ egPref ++ show n | n <- [1..16] ]

main = do
  tests <- mapM doTest (goodTests ++ badTests)
  let evalTest (nr, ans) = if ans then trace ("Test " ++ show nr ++ ": OK") False
                                  else trace ("Test " ++ show nr ++ ": FAIL") True
  when (any evalTest (zip [1..] tests)) exitFailure
