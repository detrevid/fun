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
  deriving (Eq, Ord, Show)

data Inner = Bool
           | Int
  deriving (Eq, Ord, Show)

typeInt :: Type
typeInt = TInner Int
typeBool :: Type
typeBool = TInner Bool

data TypeScheme = TypeScheme [Ident] Type
type Subst = Map.Map Ident Type
type TypeEnv = Map.Map Ident TypeScheme

data TypeVarSupplier = TypeVarSupplier [String]

getNewTypeVar' :: TypeVarSupplier -> (Type, TypeVarSupplier)
getNewTypeVar' (TypeVarSupplier ids) = (TVar $ Ident $ head ids, TypeVarSupplier $ tail ids)

newTypeVarSupplier :: TypeVarSupplier
newTypeVarSupplier = TypeVarSupplier [ "t" ++ show n | n <- [1..]]

newtype InferType a = InferType (StateT TypeVarSupplier Err a)
  deriving (Functor, Applicative, Monad)

getNewTypeVar :: InferType Type
getNewTypeVar = InferType $ state getNewTypeVar'

runInferType :: InferType a -> Err a
runInferType (InferType x) = evalStateT x newTypeVarSupplier

emptyTypeEnv :: TypeEnv
emptyTypeEnv = Map.empty

instantAll :: TypeScheme -> InferType Type
instantAll (TypeScheme ids t) = do
  vars <- replicateM (length ids) getNewTypeVar
  let sub = Map.fromList (zip ids vars)
      t' = instType sub t
  return t'

idSub :: Subst
idSub = Map.empty

lookupSub :: Subst -> Ident -> Type
lookupSub sub id = case Map.lookup id sub of
    Nothing  -> TVar id
    Just t   -> t

lookupTypeEnv :: Monad m => TypeEnv -> Ident -> m TypeScheme
lookupTypeEnv env id = case Map.lookup id env of
  Nothing  -> fail $ "Variable " ++ show id ++ "is not bound"
  Just t   -> return t

composeSubst :: Subst -> Subst -> Subst
composeSubst sub1 sub2 = Map.union (Map.map (instType sub1) sub2) sub1

composeSubsts :: [Subst] -> Subst
composeSubsts = foldl composeSubst idSub

ftv :: Type -> Set.Set Ident
ftv t = case t of
  TInner _   -> Set.empty
  TVar id    -> Set.singleton id
  TFun t1 t2 -> Set.union (ftv t1) (ftv t2)

ftvScheme :: TypeScheme -> Set.Set Ident
ftvScheme (TypeScheme ids t) = Set.difference (ftv t) (Set.fromList ids)

ftvEnv :: TypeEnv -> Set.Set Ident
ftvEnv te = Map.foldr (\x y -> Set.union y $ ftvScheme x) Set.empty te

-- instance type
instType :: Subst -> Type -> Type
instType sub t = case t of
  TVar id    -> lookupSub sub id
  TFun t1 t2 -> TFun (instType sub t1) (instType sub t2)
  _          -> t

-- instance typeScheme
instTypeScheme :: Subst -> TypeScheme -> TypeScheme
instTypeScheme sub ts = case ts of
  TypeScheme ids t -> TypeScheme ids $ instType (foldr Map.delete sub ids) t

instTypeEnv :: Subst -> TypeEnv -> TypeEnv
instTypeEnv sub env = Map.map (instTypeScheme sub) env

generalize :: TypeEnv -> Type -> TypeScheme
generalize env t = TypeScheme (Set.toList (Set.difference (ftv t) (ftvEnv env))) t

unify :: Monad m => Type -> Type -> m Subst
unify t1 t2
  | t1 == t2  =  return idSub
  | otherwise = do
    let errMsg = "Could not unify types: " ++ show t1  ++ " " ++ show t2
        unifyVar id t = if Set.member id $ ftv t then fail errMsg
                                                 else return $ Map.singleton id t
    case (t1, t2) of
      (TVar id, _)           -> unifyVar id t2
      (_, TVar id)           -> unifyVar id t1
      (TFun x y, TFun x' y') -> do
        s1 <- unify x x'
        s2 <- unify (instType s1 y) (instType s1 y')
        return $ composeSubst s2 s1
      _                      -> fail errMsg

infer :: TypeEnv -> Exp -> InferType (Type, Subst)
infer env exp = case exp of
  ELet decl exp -> do
    (env', sub1) <- inferDecl env decl
    (texp, sub2) <- infer env' exp
    return (texp, composeSubst sub2 sub1)
  EIf cond exp1 exp2 -> do
    (tcond, sub) <- infer env cond
    let env' = instTypeEnv sub env
    (texp1, sub1) <- infer env' exp1
    (texp2, sub2) <- infer (instTypeEnv sub1 env') exp2
    sub3 <- unify texp1 texp2
    return (instType sub3 texp2, composeSubsts [sub3, sub2, sub1, sub])
  ELog exp1 logopr exp2  -> inferBinOp env exp1 exp2 typeBool
  EEq exp1 eqopr exp2 -> do
    (texp1, sub1) <- infer env exp1
    (texp2, sub2) <- infer (instTypeEnv sub1 env) exp2
    sub3 <- unify (instType sub2 texp1) texp2
    let sub = composeSubsts [sub3, sub2, sub1]
    return (typeBool, sub)
  ERel exp1 relopr exp2 -> do
    (texp, sub1) <- inferBinOp env exp1 exp2 typeInt
    return (typeBool, sub1)
  EAdd exp1 addopr exp2  -> inferBinOp env exp1 exp2 typeInt
  EMul exp1 mulopr exp2  -> inferBinOp env exp1 exp2 typeInt
  ENeg exp1 -> do
    (texp, sub1) <- infer env exp1
    sub2 <- unify texp typeBool
    return (typeBool, sub2)
  EVal id -> do
    ts <- lookupTypeEnv env id
    ts' <- instantAll ts
    return (ts', idSub)
  EConst const -> return (inferConst const, idSub)
  ELam args exp1 -> case args of
    h:t -> do
      newVar <- getNewTypeVar
      let newEnv = Map.delete h env
          newEnv' = (Map.union newEnv (Map.singleton h (TypeScheme [] newVar)))
      (texp1, sub1) <- infer newEnv' $ ELam t exp1
      return (TFun (instType sub1 newVar) texp1, sub1)
    []  -> infer env exp1
  EApp exp1 exp2 -> do
    newVar <- getNewTypeVar
    (texp1, sub1) <- infer env exp1
    (texp2, sub2) <- infer (instTypeEnv sub1 env) exp2
    sub3 <- unify (instType sub2 texp1) (TFun texp2 newVar)
    return (instType sub3 newVar, composeSubsts [sub3, sub2, sub1])

inferConst :: Constant -> Type
inferConst x = case x of
 CTrue   -> typeBool
 CFalse  -> typeBool
 CInt _  -> typeInt

inferBinOp :: TypeEnv -> Exp -> Exp -> Type -> InferType (Type, Subst)
inferBinOp env exp1 exp2 t = do
  (texp1, sub1) <- infer env exp1
  (texp2, sub2) <- infer (instTypeEnv sub1 env) exp2
  sub3  <- unify (instType sub2 texp1) t
  sub4  <- unify (instType sub3 texp2) t
  let sub = composeSubsts [sub4, sub3, sub2, sub1]
  return (t, sub)

inferDecl :: TypeEnv -> Decl -> InferType (TypeEnv, Subst)
inferDecl env decl = case decl of
  DFun fname ids exp -> do
    newVar1 <- getNewTypeVar
    newVar2 <- getNewTypeVar
    let fun = TFun newVar1 newVar2
        env' = Map.delete fname env
    case (newVar1, newVar2) of
      (TVar id1, TVar id2) -> do
        let env'' = Map.insert fname (TypeScheme [] fun) env'
        (texp1, sub1) <- infer env'' (ELam ids exp)
        sub2  <- unify (instType sub1 fun) texp1
        let sub = (composeSubst sub2 sub1)
            env''' =  Map.insert fname (generalize env' (instType sub fun)) env'
        return (instTypeEnv sub env''', sub)
      _  -> fail "Internal type checker error"
  DVal id exp -> do
    (texp, sub) <- infer env exp
    let env' = Map.delete id env
        ts' = generalize env texp
        env'' = Map.insert id ts' env'
    return (instTypeEnv sub env'', sub)

checkTypesStmt :: TypeEnv -> Stmt -> InferType TypeEnv
checkTypesStmt env stmt = case stmt of
  SExp exp -> do
    (t, s) <- infer env exp
    return env
  SDecl decl -> do
     (e, s) <- inferDecl env decl
     return e

checkTypes :: Program -> Err TypeEnv
checkTypes x = case x of
  Prog stmts ->
    foldM (\x y -> runInferType $ checkTypesStmt x y) (emptyTypeEnv) stmts
