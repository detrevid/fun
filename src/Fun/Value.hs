module Fun.Value where

import Fun.BNFC.AbsFun
import Fun.BNFC.ErrM

import qualified Data.Map as Map
import qualified Control.Monad.Trans.State as StateT

data Value
  = VInt Integer
  | VBool Bool
  | VFun Fun
  | VNFun Ident Fun
  | VRec Env
  | VList [Value]
  | VBuiltIn (Value -> Eval)

data Fun = Fun { args :: [Ident], exp :: Exp, env :: Env }

type Env = Map.Map Ident Value

type Result = Err Value
type EvalM a = StateT.StateT Env Err a
type Eval = EvalM Value

emptyEnv :: Env
emptyEnv = Map.empty
