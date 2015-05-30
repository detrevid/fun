{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Type where

import AbsFun
import ErrM

import qualified Data.Map as Map
import qualified Data.Set as Set

import Control.Monad
import Control.Applicative (Applicative)
import Control.Monad.Trans.State
import Data.Foldable (foldrM)
import Debug.Trace

data Type = TInner Inner
          | TVar Ident
          | TFun Type Type
          | TRec TypeEnv
          | TExtRec TypeEnv Ident
  deriving (Eq, Ord, Show)

data Inner = Bool
           | Int
  deriving (Eq, Ord, Show)

typeInt :: Type
typeInt = TInner Int
typeBool :: Type
typeBool = TInner Bool

internalErrorMsg :: String
internalErrorMsg = "Internal error"

singletonRec :: Ident -> InferType Type
singletonRec id = do
  newVar <- getNewTypeVar
  return $ TRec $ Map.singleton id $ TypeScheme [] newVar

getVarId :: Type -> InferType Ident
getVarId t = case t of
  TVar id -> return id
  _       -> fail internalErrorMsg

makeExtRec :: Type -> InferType Type
makeExtRec t = case t of
  TRec env -> do
    newVar <- getNewTypeVar
    id <- getVarId newVar
    return $ TExtRec env id
  _    -> fail internalErrorMsg

getField :: Type -> Ident -> InferType Type
getField t id =
  case t of
    TRec env      -> case Map.lookup id env of
      Just ts -> instantAll ts
      Nothing -> fail $ "Record does not have field called: " ++ show id
    TExtRec env _ -> getField (TRec env) id
    _        -> fail internalErrorMsg

data TypeScheme = TypeScheme [Ident] Type deriving (Eq, Ord, Show)
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
  TRec env   -> ftvEnv env
  TExtRec env id -> Set.union (ftv $ TRec env) (ftv $ TVar id)

ftvScheme :: TypeScheme -> Set.Set Ident
ftvScheme (TypeScheme ids t) = Set.difference (ftv t) (Set.fromList ids)

ftvEnv :: TypeEnv -> Set.Set Ident
ftvEnv te = Map.foldr (\x y -> Set.union y $ ftvScheme x) Set.empty te

-- instance type
instType :: Subst -> Type ->  Type
instType sub t = case t of
  TVar id    -> lookupSub sub id
  TFun t1 t2 -> TFun (instType sub t1) (instType sub t2)
  TRec env   -> TRec $ instTypeEnv sub env
  TExtRec env id ->
    let env'   = instTypeEnv sub env
        instId = instType sub $ TVar id in
    case instId of
     TExtRec env'' id' -> TExtRec (env' `Map.union` env'') id'
     TRec env''        -> TRec (env' `Map.union` env'')
     TVar id'          -> TExtRec env' id'
     _                 -> TExtRec env' id
  _          -> t

-- instance typeScheme
instTypeScheme :: Subst -> TypeScheme -> TypeScheme
instTypeScheme sub ts = case ts of
  TypeScheme ids t -> TypeScheme ids $ instType (foldr Map.delete sub ids) t

instTypeEnv :: Subst -> TypeEnv -> TypeEnv
instTypeEnv sub env = Map.map (instTypeScheme sub) env

generalize :: TypeEnv -> Type -> TypeScheme
generalize env t = TypeScheme (Set.toList (Set.difference (ftv t) (ftvEnv env))) t

unify :: Type -> Type -> InferType Subst
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
      (TRec env1, TRec env2) -> do
        when (Map.keysSet env1 /= Map.keysSet env2) $ fail errMsg
        let lenv1 = Map.toAscList env1
            lenv2 = Map.toAscList env2
            (ids, ts1) = unzip lenv1
            (_, ts2) = unzip lenv2
            tss = zip ts1 ts2
        sub <- foldrM (\(x, y) sub -> do
          let ts1 = instTypeScheme sub x
              ts2 = instTypeScheme sub y
          sub1 <- unifyTypeSchemes ts1 ts2
          return $ composeSubst sub1 sub) idSub tss
        return sub
      (TRec env1, TExtRec env2 id) -> do
        when (not $ Map.keysSet env2 `Set.isSubsetOf` Map.keysSet env1) $ fail errMsg
        let commKeys = Map.keysSet env2 `Set.intersection` Map.keysSet env1
            commEnv1 = Map.filterWithKey (\x _ -> Set.member x commKeys) env1
            diffEnv1 = Map.filterWithKey (\x _ -> Set.notMember x commKeys) env1
        sub1 <- unify (TRec commEnv1) (TRec env2)
        newVar <- getNewTypeVar
        varId <- getVarId newVar
        sub2 <- unify (TVar id) (TExtRec (instTypeEnv sub1 diffEnv1) varId)
        return $ composeSubst sub2 sub1
      (TExtRec _ _, TRec _) -> unify t2 t1
      (TExtRec env1 id1, TExtRec env2 id2) -> do
        let commKeys = Map.keysSet env2 `Set.intersection` Map.keysSet env1
            diffKeys1 =  Map.keysSet env1 `Set.difference` Map.keysSet env2
            diffKeys2 =  Map.keysSet env2 `Set.difference` Map.keysSet env1
            commEnv1 = Map.filterWithKey (\x _ -> Set.member x commKeys) env1
            commEnv2 = Map.filterWithKey (\x _ -> Set.member x commKeys) env2
            diffEnv1 = Map.filterWithKey (\x _ -> Set.member x diffKeys1) env1
            diffEnv2 = Map.filterWithKey (\x _ -> Set.member x diffKeys2) env2
        sub1 <- unify (TRec commEnv1) (TRec commEnv2)
        newVar1 <- getNewTypeVar
        varId1 <- getVarId newVar1
        sub2 <- unify (TVar id1) (TExtRec (instTypeEnv sub1 diffEnv2) varId1)
        newVar2 <- getNewTypeVar
        varId2 <- getVarId newVar2
        sub3 <- unify (TVar id2) (TExtRec (instTypeEnv (composeSubst sub2 sub1) diffEnv1) varId2)
        return $ composeSubsts [sub3, sub2, sub1]
      _                      -> fail errMsg

unifyTypeSchemes :: TypeScheme -> TypeScheme -> InferType Subst
unifyTypeSchemes ts1 ts2 = do
  t1 <- instantAll ts1
  t2 <- instantAll ts2
  u <- unify t1 t2
  return u

infer :: TypeEnv -> Exp -> InferType (Type, Subst)
infer env exp = case exp of
  ELet decl exp1 -> do
    (_, sub1, env') <- inferDecl env decl
    (texp2, sub2) <- infer env' exp1
    return (texp2, composeSubst sub2 sub1)
  EIf cond exp1 exp2 -> do
    (tcond, sub1) <- infer env cond
    sub2 <- unify tcond typeBool
    let env' = instTypeEnv (composeSubst sub1 sub2) env
    (texp1, sub3) <- infer env' exp1
    (texp2, sub4) <- infer (instTypeEnv sub3 env') exp2
    let sub = composeSubsts [sub4, sub3, sub2, sub1]
        texp1' = instType sub texp1
        texp2' = instType sub texp2
    sub5 <- unify texp1' texp2'
    return (instType sub5 texp2', composeSubst sub5 sub)
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
    t <- instantAll ts
    return (t, idSub)
  ELit lit -> inferLit env lit
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
  EDot exp1 id -> do
    (texp1, sub1) <- infer env exp1
    idRec <- singletonRec id
    idRecExt <- makeExtRec idRec
    sub2 <- unify texp1 idRecExt
    let sub = composeSubst sub2 sub1
        texp1' = instType sub texp1
    t <- getField texp1' id
    return (t, sub)
  ESum exp1 exp2  -> do
    (texp1, sub1) <- infer env exp1
    (texp2, sub2) <- infer (instTypeEnv sub1 env) exp2
    newVar1 <- getNewTypeVar
    varId1 <- getVarId newVar1
    newVar2 <- getNewTypeVar
    varId2 <- getVarId newVar2
    let extExp1 = TExtRec emptyTypeEnv varId1
        extExp2 = TExtRec emptyTypeEnv varId2
    sub3 <- unify (instType sub2 texp1) extExp1
    sub4 <- unify (instType sub3 texp2) extExp2
    let sub = composeSubsts [sub4, sub3, sub2, sub1]
        extExp1' = instType sub extExp1
        extExp2' = instType sub extExp2
    sub5 <- unify extExp1' extExp2'
    let sub' = composeSubst sub5 sub
        texp1' = instType sub' texp1
        t = instType sub5 extExp1'
    return (t, sub')

inferLit :: TypeEnv -> Literal -> InferType (Type, Subst)
inferLit env x = case x of
  LTrue   -> return (typeBool, idSub)
  LFalse  -> return (typeBool, idSub)
  LInt _  -> return (typeInt, idSub)
  LRec decls -> do
     (env', inferedExps) <- foldrM (\decl (e, infs) -> do
       inf@(texp, sub, e') <- inferDecl e decl
       return (e', ((texp, sub) : infs))) (env, []) decls
     let (texps, subs) = unzip inferedExps
         sub = composeSubsts subs
         texps' = map (instTypeScheme sub) texps
         ids = map (\x -> case x of
           DFun id _ _ -> id
           DVal id _ -> id) decls
         typeEnv = Map.fromList (zip ids texps')
     return (TRec typeEnv, sub)

inferBinOp :: TypeEnv -> Exp -> Exp -> Type -> InferType (Type, Subst)
inferBinOp env exp1 exp2 t = do
  (texp1, sub1) <- infer env exp1
  (texp2, sub2) <- infer (instTypeEnv sub1 env) exp2
  sub3  <- unify (instType sub2 texp1) t
  sub4  <- unify (instType sub3 texp2) t
  let sub = composeSubsts [sub4, sub3, sub2, sub1]
  return (t, sub)

inferDecl :: TypeEnv -> Decl -> InferType (TypeScheme, Subst, TypeEnv)
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
        let ts = generalize env' (instType sub fun)
            sub = (composeSubst sub2 sub1)
            env''' =  Map.insert fname ts env'
        return (ts, sub, instTypeEnv sub env''')
      _  -> fail "Internal type checker error"
  DVal id exp -> do
    (texp, sub) <- infer env exp
    let env' = Map.delete id env
        ts = generalize env texp
        env'' = Map.insert id ts env'
    return (ts, sub, instTypeEnv sub env'')

checkTypesStmt :: TypeEnv -> Stmt -> InferType TypeEnv
checkTypesStmt env stmt = case stmt of
  SExp exp -> do
    (t, s) <- infer env exp
    return env
  SDecl decl -> do
     (t, s, e) <- inferDecl env decl
     return e

checkTypes :: Program -> Err TypeEnv
checkTypes x = case x of
  Prog stmts ->
    foldM (\x y -> runInferType $ checkTypesStmt x y) (emptyTypeEnv) stmts
