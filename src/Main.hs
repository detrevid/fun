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
      let p = pExp (myLexer s)
      in case p of
        Ok e  -> show (evalState (transExp e) Map.empty)
        Bad m -> show m
