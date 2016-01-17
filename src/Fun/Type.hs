{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Fun.Type where

import Fun.BNFC.AbsFun

import qualified Data.Map as Map

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
