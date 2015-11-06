module BuiltIn (addBuiltInsToTypeEnv, addBuiltInsToEnv) where

import AbsFun
import ErrM
import Type
import Value

import qualified Data.Map as Map
import Debug.Trace
import Control.Monad.State
import qualified Control.Monad.Trans.State as StateT

idT1 = Ident "t1"
internalErrMsg = "Internal error in built-in function"

headType = TypeScheme [idT1] $ TFun (TList $ TVar idT1) (TVar idT1)
headIdent = Ident "head"

headF :: Value -> Eval
headF (VList vals) = return $ head vals
headF _ = fail internalErrMsg

tailType = TypeScheme [idT1] $ TFun (TList $ TVar idT1) (TList $ TVar idT1)
tailIdent = Ident "tail"

tailF :: Value -> Eval
tailF (VList vals) = return $ VList $ tail vals
tailF _ = fail internalErrMsg

consType = TypeScheme [idT1] $ TFun (TVar idT1) (TFun (TList $ TVar idT1) (TList $ TVar idT1))
consIdent = Ident "cons"

consF :: Value -> Eval
consF val = return $ VBuiltIn $ (\x ->
   case x of
     VList vals -> return $ VList $ val : vals
     _ -> fail internalErrMsg)

nullType = TypeScheme [idT1] $ TFun (TList $ TVar idT1) typeBool
nullIdent = Ident "null"

nullF :: Value -> Eval
nullF (VList vals) = return $ VBool $ null vals
nullF _ = fail internalErrMsg

builtInsTypes = Map.fromList [(headIdent, headType),
                              (tailIdent, tailType),
                              (consIdent, consType),
                              (nullIdent, nullType)]
builtIns = Map.fromList [(headIdent, VBuiltIn $ headF),
                         (tailIdent, VBuiltIn $ tailF),
                         (consIdent, VBuiltIn $ consF),
                         (nullIdent, VBuiltIn $ nullF)]

addBuiltInsToEnv :: Env -> Err Env
addBuiltInsToEnv env = return $ env `Map.union` builtIns

addBuiltInsToTypeEnv :: TypeEnv -> TypeEnv
addBuiltInsToTypeEnv = flip Map.union builtInsTypes
