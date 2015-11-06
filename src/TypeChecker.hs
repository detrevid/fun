{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module TypeChecker (checkTypes) where

import AbsFun
import BuiltIn
import ErrM
import Type

import qualified Data.Map as Map
import qualified Data.Set as Set

import Control.Monad
import Control.Applicative (Applicative)
import Control.Monad.Trans.State
import Data.Foldable (foldrM)
import Debug.Trace

internalErrMsg :: String
internalErrMsg = "Internal error during type checking phase"

singletonRec :: Ident -> InferType Type
singletonRec id = do
  newVar <- getNewTypeVar
  return $ TRec $ Map.singleton id $ TypeScheme [] newVar

getVarId :: Type -> InferType Ident
getVarId t = case t of
  TVar id -> return id
  _       -> fail internalErrMsg

makeExtRec :: Type -> InferType Type
makeExtRec t = case t of
  TRec env -> do
    newVar <- getNewTypeVar
    id <- getVarId newVar
    return $ TExtRec env id
  _        -> fail internalErrMsg

getField :: Type -> Ident -> InferType Type
getField t id = do
  t' <- applySubst t
  case t' of
    TRec env      -> case Map.lookup id env of
      Just ts -> instantAll ts
      Nothing -> fail $ "Record does not have field called: " ++ show id
    TExtRec env _ -> getField (TRec env) id
    _        -> fail internalErrMsg

type Subst = Map.Map Ident Type

data TypeVarSupplier = TypeVarSupplier [String]

newTypeVarSupplier :: TypeVarSupplier
newTypeVarSupplier = TypeVarSupplier [ "t" ++ show n | n <- [1..]]

type InferState = (TypeVarSupplier, Subst, TypeEnv)

newtype InferType a = InferType (StateT InferState Err a)
  deriving (Functor, Applicative, Monad)

getNewTypeVarId' :: InferState -> (Ident, InferState)
getNewTypeVarId' (TypeVarSupplier ids, sub, env) =
  (Ident $ head ids, (TypeVarSupplier $ tail ids, sub, env))

getNewTypeVarId :: InferType Ident
getNewTypeVarId = InferType $ state getNewTypeVarId'

getNewTypeVar' :: InferState -> (Type, InferState)
getNewTypeVar' st =
  (TVar $ varId, st')
 where (varId, st') = getNewTypeVarId' st

getNewTypeVar:: InferType Type
getNewTypeVar = InferType $ state getNewTypeVar'

getSubst' :: InferState -> (Subst, InferState)
getSubst' st@(_, sub, _) = (sub, st)

getSubst :: InferType Subst
getSubst = InferType $ state getSubst'

getEnv' :: InferState -> (TypeEnv, InferState)
getEnv' st@(_, _, env) = (env, st)

getEnv :: InferType TypeEnv
getEnv = InferType $ state getEnv'

putEnv' :: TypeEnv -> InferState -> ((), InferState)
putEnv' env (tvs, sub, _) =  ((), (tvs, sub, env))

putEnv :: TypeEnv -> InferType ()
putEnv env = InferType $ state $ putEnv' env

addSubst' :: Subst -> InferState -> ((), InferState)
addSubst' sub2 (tvs, sub, env)  =
  ((), (tvs, sub', env))
 where sub' = composeSubst sub2 sub

addSubst :: Subst -> InferType ()
addSubst sub = InferType $ state $ addSubst' sub

addToEnv' :: Ident -> TypeScheme -> InferState -> ((), InferState)
addToEnv' id ts (tvs, sub, env) =
  ((), (tvs, sub, env'))
 where env' = Map.insert id ts env

addToEnv :: Ident -> TypeScheme -> InferType ()
addToEnv id ts = InferType $ state $ addToEnv' id ts

removeFromEnv' :: Ident -> InferState -> ((), InferState)
removeFromEnv' id (tvs, sub, env) =
  ((), (tvs, sub, env'))
 where env' = Map.delete id env

removeFromEnv :: Ident ->  InferType ()
removeFromEnv id = InferType $ state $ removeFromEnv' id

applySubst :: Type -> InferType Type
applySubst t = do
  sub <- getSubst
  return $ instType sub t

applySubstTypeEnv' :: TypeEnv -> InferType TypeEnv
applySubstTypeEnv' env = do
  sub <- getSubst
  return $ instTypeEnv sub env

applySubstTypeEnv :: InferType ()
applySubstTypeEnv = do
  env <- getEnv
  env' <- applySubstTypeEnv' env
  putEnv env'

runInferType :: InferType a -> Err a
runInferType (InferType x) = evalStateT x (newTypeVarSupplier, idSub, emptyEnv)

emptyEnv :: TypeEnv
emptyEnv = Map.empty

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

lookupTypeEnv' :: Monad m => TypeEnv -> Ident -> m TypeScheme
lookupTypeEnv' env id = case Map.lookup id env of
  Nothing  -> fail $ "Variable " ++ show id ++ "is not bound"
  Just t   -> return t

lookupTypeEnv :: Ident -> InferType TypeScheme
lookupTypeEnv id = do
  env <- getEnv
  lookupTypeEnv' env id

composeSubst :: Subst -> Subst -> Subst
composeSubst sub1 sub2 = Map.union (Map.map (instType sub1) sub2) sub1

composeSubsts :: [Subst] -> Subst
composeSubsts = foldl composeSubst idSub

ftv :: Type -> InferType (Set.Set Ident)
ftv t = do
  case t of
    TInner _   -> return Set.empty
    TVar id    -> return $ Set.singleton id
    TFun t1 t2 -> do
      ftvT1 <- ftv t1
      ftvT2 <- ftv t2
      return $ Set.union ftvT1 ftvT2
    TRec env   -> ftvEnv' env
    TExtRec env id -> do
      ftvId <- ftv $ TVar id
      ftvREnv <- ftv $ TRec env
      return $ Set.union ftvREnv ftvId
    TList t1   -> ftv t1

ftvScheme :: TypeScheme -> InferType (Set.Set Ident)
ftvScheme (TypeScheme ids t) = do
  ftvT <- ftv t
  return $ Set.difference ftvT (Set.fromList ids)

ftvEnv' :: TypeEnv -> InferType (Set.Set Ident)
ftvEnv' = foldrM (\x y -> do
  ftvS <- ftvScheme x
  return $ Set.union y ftvS) Set.empty

ftvEnv ::  InferType (Set.Set Ident)
ftvEnv = do
  env <- getEnv
  ftvEnv' env

instType :: Subst -> Type -> Type
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
  TList t' -> TList $ instType sub t'
  _          -> t

instTypeScheme :: Subst -> TypeScheme -> TypeScheme
instTypeScheme sub (TypeScheme ids t) = TypeScheme ids $ instType (foldr Map.delete sub ids) t

instTypeEnv :: Subst -> TypeEnv -> TypeEnv
instTypeEnv sub env = Map.map (instTypeScheme sub) env

generalize :: Type -> InferType TypeScheme
generalize t = do
  t' <- applySubst t
  ftvT <- ftv t'
  applySubstTypeEnv
  ftvE <- ftvEnv
  return $ TypeScheme (Set.toList (Set.difference ftvT ftvE)) t'

unify :: Type -> Type -> InferType ()
unify t1 t2 = do
  t1' <- applySubst t1
  t2' <- applySubst t2
  if t1' == t2' then return ()
  else do
    let errMsg = "Could not unify types: " ++ show t1'  ++ " " ++ show t2'
        unifyVar id t = do
          ftvT <- ftv t
          if Set.member id $ ftvT then fail errMsg
                                  else addSubst (Map.singleton id t)
    case (t1', t2') of
      (TVar id, _)           -> unifyVar id t2'
      (_, TVar id)           -> unifyVar id t1'
      (TFun x y, TFun x' y') -> do
        unify x x'
        unify y y'
      (TRec env1, TRec env2) -> do
        when (Map.keysSet env1 /= Map.keysSet env2) $ fail errMsg
        let lenv1 = Map.toAscList env1
            lenv2 = Map.toAscList env2
            (_, ts1) = unzip lenv1
            (_, ts2) = unzip lenv2
            tss = zip ts1 ts2
        mapM_ (\(x, y) -> unifyTypeSchemes x y) tss
      (TRec env1, TExtRec env2 id) -> do
        when (not $ Map.keysSet env2 `Set.isSubsetOf` Map.keysSet env1) $ fail errMsg
        let commKeys = Map.keysSet env2 `Set.intersection` Map.keysSet env1
            (commEnv1, diffEnv1) = Map.partitionWithKey (\x _ -> Set.member x commKeys) env1
        unify (TRec commEnv1) (TRec env2)
        newVarId <- getNewTypeVarId
        unify (TVar id) (TExtRec diffEnv1 newVarId)
      (TExtRec _ _, TRec _) -> unify t2' t1'
      (TExtRec env1 id1, TExtRec env2 id2) -> do
        let commKeys = Map.keysSet env1 `Set.intersection` Map.keysSet env2
            diffKeys1 =  Map.keysSet env1 `Set.difference` Map.keysSet env2
            diffKeys2 =  Map.keysSet env2 `Set.difference` Map.keysSet env1
            commEnv1 = Map.filterWithKey (\x _ -> Set.member x commKeys) env1
            commEnv2 = Map.filterWithKey (\x _ -> Set.member x commKeys) env2
            diffEnv1 = Map.filterWithKey (\x _ -> Set.member x diffKeys1) env1
            diffEnv2 = Map.filterWithKey (\x _ -> Set.member x diffKeys2) env2
        unify (TRec commEnv1) (TRec commEnv2)
        newVarId1 <- getNewTypeVarId
        unify (TVar id1) (TExtRec diffEnv2 newVarId1)
        newVarId2 <- getNewTypeVarId
        unify (TVar id2) (TExtRec diffEnv1 newVarId2)
      (TList t1'', TList t2'') -> unify t1'' t2''
      _                      -> fail errMsg

unifyTypeSchemes :: TypeScheme -> TypeScheme -> InferType ()
unifyTypeSchemes ts1 ts2 = do
  t1 <- instantAll ts1
  t2 <- instantAll ts2
  unify t1 t2

infer :: Exp -> InferType Type
infer exp = case exp of
  ELet decl exp1 -> do
    inferDecl decl
    infer exp1
  EIf cond exp1 exp2 -> do
    tcond <- infer cond
    unify tcond typeBool
    texp1 <- infer exp1
    texp2 <- infer exp2
    unify texp1 texp2
    return texp1
  ELog exp1 logopr exp2  -> inferBinOp exp1 exp2 typeBool
  EEq exp1 eqopr exp2 -> do
    texp1 <- infer exp1
    texp2 <- infer exp2
    unify texp1 texp2
    return typeBool
  ERel exp1 relopr exp2 -> do
    texp <- inferBinOp exp1 exp2 typeInt
    return typeBool
  EAdd exp1 addopr exp2  -> inferBinOp exp1 exp2 typeInt
  EMul exp1 mulopr exp2  -> inferBinOp exp1 exp2 typeInt
  ENeg exp1 -> do
    texp <- infer exp1
    unify texp typeBool
    return typeBool
  EVal id -> do
    ts <- lookupTypeEnv id
    instantAll ts
  ELit lit -> inferLit lit
  ELam args exp1 -> case args of
    h:t -> do
      newVar <- getNewTypeVar
      oldEnv <- getEnv
      removeFromEnv h
      addToEnv h (TypeScheme [] newVar)
      texp1 <- infer $ ELam t exp1
      putEnv oldEnv
      return $ TFun newVar texp1
    []  -> infer exp1
  EApp exp1 exp2 -> do
    newVar <- getNewTypeVar
    texp1 <- infer exp1
    texp2 <- infer exp2
    unify texp1 (TFun texp2 newVar)
    return newVar
  EDot exp1 id -> do
    texp1 <- infer exp1
    idRec <- singletonRec id
    idRecExt <- makeExtRec idRec
    unify texp1 idRecExt
    getField texp1 id
  ESum exp1 exp2 -> do
    texp1 <- infer exp1
    texp2 <- infer exp2
    newVar1 <- getNewTypeVar
    varId1 <- getVarId newVar1
    newVar2 <- getNewTypeVar
    varId2 <- getVarId newVar2
    let extExp1 = TExtRec emptyEnv varId1
        extExp2 = TExtRec emptyEnv varId2
    unify texp1 extExp1
    unify texp2 extExp2
    unify extExp1 extExp2
    return extExp1

inferLit :: Literal -> InferType Type
inferLit x = case x of
  LTrue      -> return typeBool
  LFalse     -> return typeBool
  LInt _     -> return typeInt
  LRec decls -> do
     oldEnv <- getEnv
     inferedExps <- mapM inferDecl decls
     let ids = map (\x -> case x of
           DFun id _ _ -> id
           DVal id _ -> id) decls
         typeEnv = Map.fromList (zip ids inferedExps)
     putEnv oldEnv
     return $ TRec typeEnv
  LList exps -> do
    oldEnv <- getEnv
    texps <- mapM infer exps
    putEnv oldEnv
    case texps of
      h:t  -> do
        mapM_ (unify h) t
        return $ TList $ h
      []   -> do
        newVar <- getNewTypeVar
        return (TList $ newVar)
  _          -> fail internalErrMsg

inferBinOp :: Exp -> Exp -> Type -> InferType Type
inferBinOp exp1 exp2 t = do
  texp1 <- infer exp1
  texp2 <- infer exp2
  unify texp1 t
  unify texp2 t
  return t

inferDecl :: Decl -> InferType TypeScheme
inferDecl decl = case decl of
  DFun fname ids exp -> do
    newVar1@(TVar id1) <- getNewTypeVar
    newVar2@(TVar id2) <- getNewTypeVar
    let fun = TFun newVar1 newVar2
    oldEnv <- getEnv
    removeFromEnv fname
    addToEnv fname (TypeScheme [] fun)
    texp1 <- infer (ELam ids exp)
    unify fun texp1
    removeFromEnv fname
    ts <- generalize fun
    addToEnv fname ts
    return ts
  DVal id exp -> do
    texp <- infer exp
    removeFromEnv id
    ts <- generalize texp
    addToEnv id ts
    return ts

checkTypesStmt :: Stmt -> InferType ()
checkTypesStmt stmt = case stmt of
  SExp exp -> do
    infer exp
    return ()
  SDecl decl -> do
    inferDecl decl
    return ()

checkTypes' :: Program -> InferType ()
checkTypes' (Prog stmts) = do
  putEnv $ addBuiltInsToTypeEnv emptyEnv
  mapM_ checkTypesStmt stmts

checkTypes :: Program -> Err ()
checkTypes prog =  runInferType $ checkTypes' prog
