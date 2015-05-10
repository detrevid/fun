module Interpreter where

import AbsFun
import ErrM

import qualified Data.Map as Map
import Debug.Trace
import Control.Monad.State
--import Control.Monad.Trans.State.Strict

data Value
  = VInt Integer
  | VBool Bool
  | VFun Ident Exp Env
  | VNFun Ident Ident Exp Env
  deriving (Eq,Ord)

type Result = Err Value
type Env = Map.Map Ident Result

instance Show Value where
  show r = case r of
    VInt i  -> show i
    VBool b -> show b
    VFun _ _ _ -> show "Unnamed function"
    VNFun (Ident id) _ _ _ -> show "Function: " ++ show id

failure :: Show a => a -> Result
failure x = Bad $ "Undefined case: " ++ show x

success :: Value -> Result
success x = Ok $ x

transProgram :: Program -> Result
transProgram x = case x of
  Prog stmts ->
    fst $ foldl (\x y -> runState (transStmt y) (snd x)) (Ok $ VBool True, Map.empty) stmts

transStmt :: Stmt -> State Env Result
transStmt x = case x of
  SExp exp  -> transExp exp
  DExp decl  -> transDecl decl

transDecl :: Decl -> State Env Result
transDecl x = case x of
  DFun id1 id2 exp -> do
    oldEnv <- get
    let fun = VNFun id1 id2 exp oldEnv in do
      modify (Map.insert id1 (Ok fun))
      return $ Ok $ fun

transExp :: Exp -> State Env Result
transExp x =
  case x of
    ELet id exp1 exp2  -> do
      e1 <- transExp exp1
      oldEnv <- get
      modify (Map.insert id e1)
      result <- transExp exp2
      put oldEnv
      return result
    EIf cond exp1 exp2  -> do
      Ok (VBool c) <- transExp cond
      if c then transExp exp1
           else transExp exp2
    ELog exp1 logopr exp2  -> do
      evalBinOpExp (transLogOpr logopr) exp1 exp2
    EEq exp1 eqopr exp2  -> do
      evalBinOpExp (transEqOpr eqopr) exp1 exp2
    ERel exp1 relopr exp2  -> do
      evalBinOpExp (transRelOpr relopr) exp1 exp2
    EAdd exp1 addopr exp2  -> do
      evalBinOpExp (transAddOpr addopr) exp1 exp2
    EMul exp1 mulopr exp2  -> do
      evalBinOpExp (transMulOpr mulopr) exp1 exp2
    ENeg exp  -> do
      evalNeg exp
    EVal id -> do
      val <- gets (Map.lookup id)
      case val of
        Just v -> return v
        Nothing -> return $ Bad $ "Undeclared variable: " ++ show id
    EConst const  -> do
      transConstant const
    ELam id exp  -> do
      env <- get
      return $ transLam id exp env
    EApp exp1 exp2  -> do
      transApp exp1 exp2

evalBinOpExp :: (Value -> Value -> Result) -> Exp -> Exp -> State Env Result
evalBinOpExp op exp1 exp2 = do
  Ok e1 <- transExp exp1
  Ok e2 <- transExp exp2
  return $ op e1 e2

evalNeg :: Exp -> State Env Result
evalNeg exp = do
  Ok e <- transExp exp
  case e of
    VBool b -> return $ success $ VBool $ not b
    _       -> return $ failure exp

transConstant :: Constant -> State Env Result
transConstant x = do
 case x of
   CTrue  -> return $ Ok $ VBool True
   CFalse  -> return $ Ok $ VBool False
   CInt n  -> return $ Ok $ VInt n


transLogOpr :: LogOpr -> Value -> Value -> Result
transLogOpr x a b =
  case (x, a, b) of
    (OOr, VBool v1, VBool v2)  -> success $ VBool $ v1 || v2
    (OAnd, VBool v1, VBool v2) -> success $ VBool $ v1 && v2
    _                          -> failure (x, a, b)


transEqOpr :: EqOpr -> Value -> Value -> Result
transEqOpr x a b =
  case (x, a, b) of
    (OEq, VBool v1, VBool v2)  -> success $ VBool $ v1 == v2
    (ONeq, VBool v1, VBool v2) -> success $ VBool $ v1 /= v2
    (OEq, VInt v1, VInt v2)    -> success $ VBool $ v1 == v2
    (ONeq, VInt v1, VInt v2)   -> success $ VBool $ v1 /= v2
    _                          -> failure (x, a, b)

transRelOpr :: RelOpr -> Value -> Value -> Result
transRelOpr x a b =
  case (x, a, b) of
    (OLes, VInt v1, VInt v2) -> success $ VBool $ v1 < v2
    (OGrt, VInt v1, VInt v2) -> success $ VBool $ v1 > v2
    (OLeq, VInt v1, VInt v2) -> success $ VBool $ v1 <= v2
    (OGeq, VInt v1, VInt v2) -> success $ VBool $ v1 >= v2
    _                        -> failure (x, a, b)

transAddOpr :: AddOpr -> Value -> Value -> Result
transAddOpr x a b =
  case (x, a, b) of
    (OAdd, VInt v1, VInt v2) -> success $ VInt $ v1 + v2
    (OSub, VInt v1, VInt v2) -> success $ VInt $ v1 - v2
    _                        -> failure (x, a, b)

transMulOpr :: MulOpr -> Value -> Value -> Result
transMulOpr x a b =
  case (x, a, b) of
    (OMul, VInt v1, VInt v2) -> success $ VInt $ v1 * v2
    (ODiv, VInt v1, VInt v2) -> success $ VInt $ v1 `quot` v2
    _                        -> failure (x, a, b)

transLam :: Ident -> Exp -> Env -> Result
transLam arg exp env = do
  success $ VFun arg exp env

transApp :: Exp -> Exp -> State Env Result
transApp exp1 exp2 = do
 f <- transExp exp1
 case f of
   Ok (VFun arg exp3 env) -> do
     oldEnv <- get
     e <- transExp exp2
     put env
     modify (Map.insert arg e)
     result <- transExp exp3
     put oldEnv
     return $ result
   Ok (VNFun name arg exp3 env) -> do
     oldEnv <- get
     e <- transExp exp2
     put env
     modify (Map.insert arg e)
     modify (Map.insert name f)
     result <- transExp exp3
     put oldEnv
     return $ result
   _ -> return $ Bad $ "Expression is not a function: " ++ show exp1