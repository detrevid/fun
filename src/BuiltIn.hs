module BuiltIn where

import AbsFun
import ErrM
import Type
import Value

import qualified Data.Map as Map
import Debug.Trace
import Control.Monad.State
import qualified Control.Monad.Trans.State as StateT


headType = TypeScheme [Ident "t1"] $ TFun (TList $ TVar $ Ident "t1") (TVar $ Ident "t1")
headIdent = Ident "head"

headF :: Value -> Eval
headF (VList vals) = return $ head vals
headF _ = fail "internalError"

tailType = TypeScheme [Ident "t1"] $ TFun (TList $ TVar $ Ident "t1") (TList $ TVar $ Ident "t1")
tailIdent = Ident "tail"

tailF :: Value -> Eval
tailF (VList vals) = return $ VList $ tail vals
tailF _ = fail "internalError"

builtInsTypes = Map.fromList [(headIdent, headType), (tailIdent, tailType)]
builtIns = Map.fromList [(headIdent, VBuiltIn $ headF), (tailIdent, VBuiltIn $ tailF)]

addBuiltInsToEnv :: Env -> Err Env
addBuiltInsToEnv env =
  return $ env `Map.union` builtIns

addBuiltInsToTypeEnv :: TypeEnv -> Err TypeEnv
addBuiltInsToTypeEnv env =
  return $ env `Map.union` builtInsTypes