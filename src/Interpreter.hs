{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Interpreter (transProgram) where

import AbsFun
import ErrM
import Type
import Preparator

import qualified Data.Map as Map
import Debug.Trace
import Control.Monad.State
import qualified Control.Monad.Trans.State as StateT

data Value
  = VInt Integer
  | VBool Bool
  | VFun Fun
  | VNFun Ident Fun
  | VRec Env
  | VList [Value]
  deriving (Eq)

data Fun = Fun { args :: [Ident], exp :: Exp, env :: Env } deriving (Eq)

type Result = Err Value
type Env = Map.Map Ident Value
type EvalM a = StateT.StateT Env Err a
type Eval = EvalM Value

internalErrMsg = "Internal error during interpreting phase"

emptyEnv :: Env
emptyEnv = Map.empty

instance Show Value where
  show r = case r of
    VInt i  -> show i
    VBool b -> show b
    VFun _ -> show "Unnamed function"
    VNFun (Ident id) _ -> show "Function: " ++ show id
    VRec env -> "{" ++ show env ++ "}"
    VList vals -> show vals

transProgram :: Program -> Result
transProgram p = do
  p' <- prepareProgram p
  checkTypes p'
  case p' of
    Prog stmts -> do
      (v, _) <- foldM (\(_, env') y -> runStateT (transStmt y) env')  (VBool True, emptyEnv) stmts
      return v

transStmt :: Stmt -> Eval
transStmt x = case x of
  SExp exp  -> transExp exp
  SDecl decl  -> transDecl decl

transDecl :: Decl -> Eval
transDecl x = case x of
  DFun id args exp -> do
    oldEnv <- get
    let fun = VNFun id $ Fun args exp oldEnv
    modify (Map.insert id fun)
    return $ fun
  DVal id exp -> do
    e1 <- transExp exp
    modify (Map.insert id e1)
    return e1

transExp :: Exp -> Eval
transExp x = case x of
  ELet decl exp2  -> do
    oldEnv <- get
    e1 <- transDecl decl
    result <- transExp exp2
    put oldEnv
    return result
  EIf cond exp1 exp2  -> do
    c <- transExp cond
    case c of
      VBool b -> if b then transExp exp1
                      else transExp exp2
      _       -> fail internalErrMsg
  ELog exp1 logopr exp2  -> evalBinOpExp (transLogOpr logopr) exp1 exp2
  EEq exp1 eqopr exp2  -> evalBinOpExp (transEqOpr eqopr) exp1 exp2
  ERel exp1 relopr exp2  -> evalBinOpExp (transRelOpr relopr) exp1 exp2
  EAdd exp1 addopr exp2  -> evalBinOpExp (transAddOpr addopr) exp1 exp2
  EMul exp1 mulopr exp2  -> evalBinOpExp (transMulOpr mulopr) exp1 exp2
  ENeg exp  -> evalNeg exp
  EVal id -> do
    val <- gets (Map.lookup id)
    case val of
      Just v -> return v
      Nothing -> fail internalErrMsg
  ELit lit  -> transLiteral lit
  ELam args exp -> do
    v <- transLam args exp
    return $ v
  EApp exp1 exp2  -> transApp exp1 exp2
  EDot exp id -> do
    e <- transExp exp
    case e of
      VRec env1 -> case Map.lookup id env1 of
        Just v   -> return v
        Nothing  -> fail internalErrMsg
      _        -> fail internalErrMsg
  ESum exp1 exp2  -> do
    e1 <- transExp exp1
    e2 <- transExp exp2
    case (e1, e2) of
      (VRec env1, VRec env2) -> do
        return $ VRec $ Map.union env2 env1
      _                      -> fail internalErrMsg
  _  -> fail internalErrMsg

evalBinOpExp :: (Value -> Value -> Eval) -> Exp -> Exp -> Eval
evalBinOpExp op exp1 exp2 = do
  e1 <- transExp exp1
  e2 <- transExp exp2
  sol <- op e1 e2
  return sol

evalNeg :: Exp -> Eval
evalNeg exp = do
  e <- transExp exp
  case e of
    VBool b -> return $ VBool $ not b
    _       -> fail internalErrMsg

transLiteral :: Literal -> Eval
transLiteral x = case x of
  LTrue   -> return $ VBool True
  LFalse  -> return $ VBool False
  LInt n  -> return $ VInt n
  LRec decls  -> do
    vals <-  mapM transDecl decls
    let ids = map (\x -> case x of
           DFun id _ _ -> id
           DVal id _ -> id) decls
        env = Map.fromList $ zip ids vals
    return $ VRec env
  LList exps -> do
    transedExp <- mapM transExp exps
    return $ VList $ transedExp
  _       -> fail internalErrMsg


transLogOpr :: LogOpr -> Value -> Value -> Eval
transLogOpr x a b = case (x, a, b) of
  (OOr, VBool v1, VBool v2)  -> return $ VBool $ v1 || v2
  (OAnd, VBool v1, VBool v2) -> return $ VBool $ v1 && v2
  _                          -> fail internalErrMsg

evalEqOpr :: Eq a => EqOpr -> a -> a -> Bool
evalEqOpr opr = case opr of
  OEq -> (==)
  ONeq -> (/=)

transEqOpr :: EqOpr -> Value -> Value -> Eval
transEqOpr opr a b = case (a, b) of
  (VBool v1, VBool v2)  -> return $ VBool $ (evalEqOpr opr) v1 v2
  (VInt v1, VInt v2)    -> return $ VBool $ (evalEqOpr opr) v1 v2
  _                     -> fail internalErrMsg

evalRelOpr :: RelOpr -> Integer -> Integer -> Bool
evalRelOpr opr = case opr of
  OLes -> (<)
  OGrt -> (>)
  OLeq -> (<=)
  OGeq -> (>=)

transRelOpr :: RelOpr -> Value -> Value -> Eval
transRelOpr opr a b = case (a, b) of
  (VInt v1, VInt v2) -> return $ VBool $ (evalRelOpr opr) v1 v2
  _                  -> fail internalErrMsg

evalAddOpr :: AddOpr -> Integer -> Integer -> Integer
evalAddOpr opr = case opr of
  OAdd -> (+)
  OSub -> (-)

transAddOpr :: AddOpr -> Value -> Value -> Eval
transAddOpr opr a b = case (a, b) of
  (VInt v1, VInt v2) -> return $ VInt $ (evalAddOpr opr) v1 v2
  _                  -> fail internalErrMsg

transMulOpr :: MulOpr -> Value -> Value -> Eval
transMulOpr x a b = case (x, a, b) of
  (OMul, VInt v1, VInt v2) -> return $ VInt $ v1 * v2
  (ODiv, VInt v1, VInt v2) ->
    if v2 /= 0 then return $ VInt $ v1 `quot` v2
               else fail "Division by zero"
  _                       -> fail internalErrMsg

transLam :: [Ident] -> Exp -> Eval
transLam args exp = do
  env <- get
  return $ VFun $ Fun args exp env

funApp :: Fun -> Exp -> Eval
funApp (Fun args exp env) exp2 = do
  oldEnv <- get
  e <- transExp exp2
  put env
  modify (Map.insert (head args) e)
  let newArgs = tail args
  if not $ null newArgs
    then do
      newEnv <- get
      let f = VFun $ Fun newArgs exp newEnv
      put oldEnv
      return f
    else do
      result <- transExp exp
      put oldEnv
      return result

transApp :: Exp  -> Exp -> Eval
transApp exp1 exp2 = do
  f <- transExp exp1
  case f of
    VFun f' -> funApp f' exp2
    f'@(VNFun name (Fun args exp3 env)) ->
      funApp (Fun args exp3 (Map.insert name f' env)) exp2
    _     -> fail internalErrMsg
