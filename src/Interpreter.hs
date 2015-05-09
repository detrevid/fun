module Interpreter where

import AbsFun
import ErrM

import Data.Map as Map
import Control.Monad.State

data Value
  = VInt Integer
  | VBool Bool
  deriving (Eq,Ord,Show)

type Result = Err Value
type Env = Map.Map String Int

failure :: Show a => a -> Result
failure x = Bad $ "Undefined case: " ++ show x

success :: Value -> Result
success x = Ok $ x

transExp :: Exp -> Result
transExp x = case x of
  ELog exp1 logopr exp2  -> evalBinOpExp (transLogOpr logopr) exp1 exp2
  EEq exp1 eqopr exp2  -> evalBinOpExp (transEqOpr eqopr) exp1 exp2
  ERel exp1 relopr exp2  -> evalBinOpExp (transRelOpr relopr) exp1 exp2
  EConst const  -> transConstant const

evalBinOpExp :: (Value -> Value -> Result) -> Exp -> Exp -> Result
evalBinOpExp op exp1 exp2 = do
  e1 <- transExp exp1
  e2 <- transExp exp2
  op e1 e2

transConstant :: Constant -> Result
transConstant x = do
 case x of
   CTrue  -> return $ VBool True
   CFalse  -> return $ VBool False
   CInt n  -> return $ VInt n


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
    (OEq, VInt v1, VInt v2)  -> success $ VBool $ v1 == v2
    (ONeq, VInt v1, VInt v2) -> success $ VBool $ v1 /= v2
    _                          -> failure (x, a, b)

transRelOpr :: RelOpr -> Value -> Value -> Result
transRelOpr x a b =
  case (x, a, b) of
    (OLes, VInt v1, VInt v2)  -> success $ VBool $ v1 < v2
    (OGrt, VInt v1, VInt v2) -> success $ VBool $ v1 > v2
    (OLeq, VInt v1, VInt v2)  -> success $ VBool $ v1 <= v2
    (OGeq, VInt v1, VInt v2) -> success $ VBool $ v1 >= v2
    _                          -> failure (x, a, b)
