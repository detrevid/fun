module Main where

    import LexFun
    import ParFun
    import AbsFun
    import Interpreter

    import Control.Monad.State
    import Data.Map as Map
    import ErrM
  
    main = do
      interact calc
      putStrLn ""

    calc s =
      let p = pProgram (myLexer s)
      in case p of
        Ok prog -> show $ transProgram prog
        Bad m -> show m
