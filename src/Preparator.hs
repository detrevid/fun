module Preparator (prepareProgram) where

import AbsFun
import ErrM

prepareProgram :: Program -> Err Program
prepareProgram p = case p of
  Prog stmts -> do
    preparedStms <- mapM prepareStmt stmts
    return $ Prog preparedStms

prepareStmt :: Stmt -> Err Stmt
prepareStmt s = case s of
  SExp exp -> do
    preparedExp <- prepareExp exp
    return $ SExp $ preparedExp
  _        -> return s

prepareExp :: Exp -> Err Exp
prepareExp exp = case exp of
  _ -> return exp
