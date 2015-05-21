{-# LANGUAGE GADTs #-}
module Interpreter where

import AbsFun
import ErrM
import Type

import qualified Data.Map as Map
import Debug.Trace
import Control.Monad.State

data Value
  = VInt Integer
  | VBool Bool
  | VFun Fun
  | VNFun Ident Fun
  deriving (Eq)

data Fun = Fun { args :: [Ident], exp :: Exp, env :: Env } deriving (Eq)

type Result = Err Value
type Env = Map.Map Ident Value
type Eval = State Env Result

emptyEnv :: Env
emptyEnv = Map.empty

instance Show Value where
  show r = case r of
    VInt i  -> show i
    VBool b -> show b
    VFun _ -> show "Unnamed function"
    VNFun (Ident id) _ -> show "Function: " ++ show id

failure :: Show a => a -> Result
failure x = Bad $ "Undefined case: " ++ show x

success :: Value -> Result
success x = Ok $ x

transProgram :: Program -> Result
transProgram x = do
  checkTypes x
  case x of
    Prog stmts ->
      fst $ foldl (\x y -> runState (transStmt y) (snd x)) (Ok $ VBool True, emptyEnv) stmts

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
    return $ Ok $ fun
  DVal id exp -> do
    e1 <- transExp exp
    case e1 of
      Ok e1' -> do
        modify (Map.insert id e1')
        return e1
      Bad m -> return $ Bad m

transExp :: Exp -> Eval
transExp x = case x of
  ELet decl exp2  -> do
    oldEnv <- get
    e1 <- transDecl decl
    case e1 of
      Ok e1' -> do
        result <- transExp exp2
        put oldEnv
        return result
      Bad m -> return $ Bad m
  EIf cond exp1 exp2  -> do
    Ok (VBool c) <- transExp cond
    if c then transExp exp1
         else transExp exp2
  ELog exp1 logopr exp2  -> evalBinOpExp (transLogOpr logopr) exp1 exp2
  EEq exp1 eqopr exp2  -> evalBinOpExp (transEqOpr eqopr) exp1 exp2
  ERel exp1 relopr exp2  -> evalBinOpExp (transRelOpr relopr) exp1 exp2
  EAdd exp1 addopr exp2  -> evalBinOpExp (transAddOpr addopr) exp1 exp2
  EMul exp1 mulopr exp2  -> evalBinOpExp (transMulOpr mulopr) exp1 exp2
  ENeg exp  -> evalNeg exp
  EVal id -> do
    val <- gets (Map.lookup id)
    case val of
      Just v -> return $ Ok $ v
      Nothing -> return $ Bad $ "Undeclared variable: " ++ show id
  EConst const  -> transConstant const
  ELam args exp -> do
    env <- get
    return $ transLam args exp env
  EApp exp1 exp2  -> transApp exp1 exp2

evalBinOpExp :: (Value -> Value -> Result) -> Exp -> Exp -> Eval
evalBinOpExp op exp1 exp2 = do
  e1 <- transExp exp1
  e2 <- transExp exp2
  case (e1, e2) of
    (Ok le, Ok re) -> return $ op le re
    (Bad m, _) -> return $ Bad m
    (_, Bad m) -> return $ Bad m

evalNeg :: Exp -> Eval
evalNeg exp = do
  e <- transExp exp
  case e of
    Ok (VBool b) -> return $ success $ VBool $ not b
    Bad m        -> return $ Bad m
    _            -> return $ Bad $ "Cannot apply negation to the expression: " ++ show exp

transConstant :: Constant -> Eval
transConstant x = case x of
  CTrue   -> return $ Ok $ VBool True
  CFalse  -> return $ Ok $ VBool False
  CInt n  -> return $ Ok $ VInt n


transLogOpr :: LogOpr -> Value -> Value -> Result
transLogOpr x a b = case (x, a, b) of
  (OOr, VBool v1, VBool v2)  -> success $ VBool $ v1 || v2
  (OAnd, VBool v1, VBool v2) -> success $ VBool $ v1 && v2
  _                          -> failure (x, a, b)

evalEqOpr :: Eq a => EqOpr -> a -> a -> Bool
evalEqOpr opr = case opr of
  OEq -> (==)
  ONeq -> (/=)

transEqOpr :: EqOpr -> Value -> Value -> Result
transEqOpr opr a b = case (a, b) of
  (VBool v1, VBool v2)  -> success $ VBool $ (evalEqOpr opr) v1 v2
  (VInt v1, VInt v2)    -> success $ VBool $ (evalEqOpr opr) v1 v2
  _                     -> failure (a, b)

evalRelOpr :: RelOpr -> Integer -> Integer -> Bool
evalRelOpr opr = case opr of
  OLes -> (<)
  OGrt -> (>)
  OLeq -> (<=)
  OGeq -> (>=)

transRelOpr :: RelOpr -> Value -> Value -> Result
transRelOpr opr a b = case (a, b) of
  (VInt v1, VInt v2) -> success $ VBool $ (evalRelOpr opr) v1 v2
  _                  -> failure (a, b)

evalAddOpr :: AddOpr -> Integer -> Integer -> Integer
evalAddOpr opr = case opr of
  OAdd -> (+)
  OSub -> (-)

transAddOpr :: AddOpr -> Value -> Value -> Result
transAddOpr opr a b = case (a, b) of
  (VInt v1, VInt v2) -> success $ VInt $ (evalAddOpr opr) v1 v2
  _                  -> failure (opr, a, b)

transMulOpr :: MulOpr -> Value -> Value -> Result
transMulOpr x a b = case (x, a, b) of
  (OMul, VInt v1, VInt v2) -> success $ VInt $ v1 * v2
  (ODiv, VInt v1, VInt v2) ->
    if v2 /= 0 then success $ VInt $ v1 `quot` v2
               else Bad $ "Division by zero"
  _                       -> failure (x, a, b)

transLam :: [Ident] -> Exp -> Env -> Result
transLam args exp env = do
  (success $ VFun $ Fun args exp env)

funApp :: Fun -> Exp -> Eval
funApp (Fun args exp env) exp2 = do
  oldEnv <- get
  e <- transExp exp2
  case e of
    Ok e' -> do
      put env
      modify (Map.insert (head args) e')
      let newArgs = tail args
      if not $ null newArgs
        then do
          newEnv <- get
          let f = VFun $ Fun newArgs exp newEnv
          put oldEnv
          return $ Ok $ f
        else do
          result <- transExp exp
          put oldEnv
          return $ result
    Bad m -> return $ Bad m

transApp :: Exp  -> Exp -> Eval
transApp exp1 exp2 = do
  f <- transExp exp1
  case f of
    Ok (VFun f') -> funApp f' exp2
    Ok f'@(VNFun name (Fun args exp3 env)) ->
      funApp (Fun args exp3 (Map.insert name f' env)) exp2
    Bad m -> return $ Bad m
    _     -> return $ Bad $ "Expression is not a function: " ++ show f
