module Preparator (prepareProgram) where

import AbsFun
import ErrM

internalErrMsg = "Internal error during preparation stage"

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
  SDecl decl -> do
    preparedDecl <- prepareDecl decl
    return $ SDecl $ preparedDecl

prepareDecl :: Decl -> Err Decl
prepareDecl d = case d of
  DFun id ids exp -> do
    preparedExp <- prepareExp exp
    return $ DFun id ids preparedExp
  DVal id exp -> do
    preparedExp <- prepareExp exp
    return $  DVal id preparedExp

prepareExp :: Exp -> Err Exp
prepareExp exp = case exp of
  ELet decl exp -> do
    pexp <- prepareExp exp
    return $ ELet decl pexp
  EIf exp1 exp2 exp3 -> do
    pexp1 <- prepareExp exp1
    pexp2 <- prepareExp exp2
    pexp3 <- prepareExp exp3
    return $ EIf pexp1 pexp2 pexp3
  ELam ids exp -> do
    pexp <- prepareExp exp
    return $ ELam ids pexp
  ELog exp1 logopr exp2 -> do
    pexp1 <- prepareExp exp1
    pexp2 <- prepareExp exp2
    return $ ELog pexp1 logopr pexp2
  EEq exp1 eqopr exp2 -> do
    pexp1 <- prepareExp exp1
    pexp2 <- prepareExp exp2
    return $ EEq pexp1 eqopr pexp2
  ERel exp1 relopr exp2 -> do
    pexp1 <- prepareExp exp1
    pexp2 <- prepareExp exp2
    return $ ERel pexp1 relopr pexp2
  EAdd exp1 addopr exp2 -> do
    pexp1 <- prepareExp exp1
    pexp2 <- prepareExp exp2
    return $ EAdd pexp1 addopr pexp2
  EMul exp1 mulopr exp2 -> do
    pexp1 <- prepareExp exp1
    pexp2 <- prepareExp exp2
    return $ EMul pexp1 mulopr pexp2
  ENeg exp -> do
    pexp <- prepareExp exp
    return $ ENeg pexp
  ESum exp1 exp2 -> do
    pexp1 <- prepareExp exp1
    pexp2 <- prepareExp exp2
    return $ ESum pexp1 pexp2
  EApp exp1 exp2 -> do
    pexp1 <- prepareExp exp1
    pexp2 <- prepareExp exp2
    return $ EApp pexp1 pexp2
  EDot exp1 id -> do
    pexp1 <- prepareExp exp1
    return $ EDot pexp1 id
  EVal id  -> return $ EVal id
  ELit (LTup exp1 exps) -> do
    let exps' = exp1 : exps
        decls = map (\(i, e) -> DVal (Ident i) e) (zip [ "e_" ++ show n | n <- [1..]] exps')
    return $ ELit $ LRec decls
  EInv exp1 -> do
     pexp1 <- prepareExp exp1
     return $ EAdd (ELit $ LInt 0) OSub pexp1
  _ -> return exp
