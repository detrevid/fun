module Fun.Main where

import Fun.BNFC.ErrM
import Fun.BNFC.ParFun
import Fun.Interpreter

main :: IO ()
main = do
  interact interpret
  putStrLn ""

interpret :: String -> String
interpret s =
  let p = pProgram (myLexer s)
  in case p of
    Ok prog -> show $ transProgram prog
    Bad m -> show m
