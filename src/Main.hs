module Main where

    import LexFun
    import ParFun
    import AbsFun
    import Interpreter
  
    import ErrM
  
    main = do
      interact calc
      putStrLn ""

    calc s =
      let p = pExp (myLexer s)
      in case p of
        Ok e  -> show (transExp e)
        Bad m -> show m
