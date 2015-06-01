{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Type where

import AbsFun
import ErrM

import qualified Data.Map as Map
import qualified Data.Set as Set

import Control.Monad
import Control.Applicative (Applicative)
import Control.Monad.Trans.State
import Debug.Trace

data Type = TInner Inner
          | TVar Ident
          | TFun Type Type
          | TRec TypeEnv
          | TExtRec TypeEnv Ident
          | TList Type
  deriving (Eq, Ord, Show)

data Inner = Bool
           | Int
  deriving (Eq, Ord, Show)

typeInt :: Type
typeInt = TInner Int
typeBool :: Type
typeBool = TInner Bool

data TypeScheme = TypeScheme [Ident] Type deriving (Eq, Ord, Show)
type TypeEnv = Map.Map Ident TypeScheme