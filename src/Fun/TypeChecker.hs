{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Fun.TypeChecker (checkTypes) where

import Fun.BNFC.AbsFun
import Fun.BNFC.ErrM
import Fun.BuiltIn
import Fun.Type

import qualified Data.Map as Map
import qualified Data.Set as Set

import Control.Monad
import Control.Applicative (Applicative)
import Control.Monad.State
import Data.Foldable (foldrM)

internalErrMsg :: String
internalErrMsg = "Internal error during type checking phase"

singletonRec :: Ident -> InferType Type
singletonRec ident = do
  newVar <- getNewTypeVar
  return $ TRec $ Map.singleton ident $ TypeScheme [] newVar

getVarId :: Type -> InferType Ident
getVarId t = case t of
  TVar ident -> return ident
  _       -> fail internalErrMsg

makeExtRec :: Type -> InferType Type
makeExtRec t = case t of
  TRec env -> do
    newVar <- getNewTypeVar
    ident <- getVarId newVar
    return $ TExtRec env ident
  _        -> fail internalErrMsg

getField :: Type -> Ident -> InferType Type
getField t ident = do
  t' <- applySubst t
  case t' of
    TRec env -> case Map.lookup ident env of
      Just ts -> instantAll ts
      Nothing -> fail $ "Record does not have a field called: " ++ show ident
    TExtRec env _ -> getField (TRec env) ident
    _  -> fail internalErrMsg

type Subst = Map.Map Ident Type

data TypeVarSupplier = TypeVarSupplier [String]

newTypeVarSupplier :: TypeVarSupplier
newTypeVarSupplier = TypeVarSupplier [ "t" ++ show n | n <- [1..]]

data InferState = InferState { supplier :: TypeVarSupplier, substitution :: Subst, environment :: TypeEnv}

defaultInferState = InferState { supplier = newTypeVarSupplier, substitution = idSub, environment =  emptyEnv }

newtype InferType a = InferType (StateT InferState Err a)
  deriving (Functor, Applicative, Monad, MonadState InferState)

getNewTypeVarId' :: InferState -> (Ident, InferState)
getNewTypeVarId' (InferState (TypeVarSupplier idents) sub env) =
  (Ident $ head idents, InferState (TypeVarSupplier $ tail idents) sub env)

getNewTypeVarId :: InferType Ident
getNewTypeVarId = state getNewTypeVarId'

getNewTypeVar' :: InferState -> (Type, InferState)
getNewTypeVar' st =
  (TVar $ varId, st')
 where (varId, st') = getNewTypeVarId' st

getNewTypeVar:: InferType Type
getNewTypeVar = state getNewTypeVar'

getSubst :: InferType Subst
getSubst = gets substitution

getEnv :: InferType TypeEnv
getEnv = gets environment

putEnv :: TypeEnv -> InferType ()
putEnv env = modify $ \s -> s { environment = env }

addSubst :: Subst -> InferType ()
addSubst sub = modify $ \s -> s { substitution = composeSubst sub $ substitution s }

addToEnv :: Ident -> TypeScheme -> InferType ()
addToEnv ident ts = modify $ \s -> s { environment = Map.insert ident ts $ environment s }

removeFromEnv :: Ident ->  InferType ()
removeFromEnv ident = modify $ \s -> s { environment = Map.delete ident $ environment s }

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
runInferType (InferType x) = evalStateT x defaultInferState

emptyEnv :: TypeEnv
emptyEnv = Map.empty

instantAll :: TypeScheme -> InferType Type
instantAll (TypeScheme idents t) = do
  vars <- replicateM (length idents) getNewTypeVar
  let sub = Map.fromList (zip idents vars)
      t' = instType sub t
  return t'

idSub :: Subst
idSub = Map.empty

lookupSub :: Subst -> Ident -> Type
lookupSub sub ident = maybe (TVar ident) id $ Map.lookup ident sub

lookupTypeEnv' :: Monad m => TypeEnv -> Ident -> m TypeScheme
lookupTypeEnv' env ident =
  maybe (fail $ "Variable " ++ show ident ++ "is not bound") (return . id) $ Map.lookup ident env

lookupTypeEnv :: Ident -> InferType TypeScheme
lookupTypeEnv ident = do
  env <- getEnv
  lookupTypeEnv' env ident

composeSubst :: Subst -> Subst -> Subst
composeSubst sub1 sub2 = Map.union (Map.map (instType sub1) sub2) sub1

ftv :: Type -> InferType (Set.Set Ident)
ftv t = do
  case t of
    TInner _   -> return Set.empty
    TVar ident    -> return $ Set.singleton ident
    TFun t1 t2 -> do
      ftvT1 <- ftv t1
      ftvT2 <- ftv t2
      return $ Set.union ftvT1 ftvT2
    TRec env   -> ftvEnv' env
    TExtRec env ident -> do
      ftvId <- ftv $ TVar ident
      ftvREnv <- ftv $ TRec env
      return $ Set.union ftvREnv ftvId
    TList t1   -> ftv t1

ftvScheme :: TypeScheme -> InferType (Set.Set Ident)
ftvScheme (TypeScheme idents t) = do
  ftvT <- ftv t
  return $ Set.difference ftvT (Set.fromList idents)

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
  TVar ident        -> lookupSub sub ident
  TFun t1 t2        -> TFun (instType sub t1) (instType sub t2)
  TRec env          -> TRec $ instTypeEnv sub env
  TExtRec env ident ->
    let env'   = instTypeEnv sub env
        instId = instType sub $ TVar ident in
    case instId of
      TExtRec env'' ident' -> TExtRec (env' `Map.union` env'') ident'
      TRec env''           -> TRec (env' `Map.union` env'')
      TVar ident'          -> TExtRec env' ident'
      _                    -> TExtRec env' ident
  TList t'          -> TList $ instType sub t'
  _                 -> t

instTypeScheme :: Subst -> TypeScheme -> TypeScheme
instTypeScheme sub (TypeScheme idents t) = TypeScheme idents $ instType (foldr Map.delete sub idents) t

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
        unifyVar ident t = do
          ftvT <- ftv t
          if Set.member ident $ ftvT then fail errMsg
                                     else addSubst (Map.singleton ident t)
    case (t1', t2') of
      (TVar ident, _) -> unifyVar ident t2'
      (_, TVar ident) -> unifyVar ident t1'
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
      (TRec env1, TExtRec env2 ident) -> do
        when (not $ Map.keysSet env2 `Set.isSubsetOf` Map.keysSet env1) $ fail errMsg
        let commKeys = Map.keysSet env2 `Set.intersection` Map.keysSet env1
            (commEnv1, diffEnv1) = Map.partitionWithKey (\x _ -> Set.member x commKeys) env1
        unify (TRec commEnv1) (TRec env2)
        newVarId <- getNewTypeVarId
        unify (TVar ident) (TExtRec diffEnv1 newVarId)
      (TExtRec _ _, TRec _) -> unify t2' t1'
      (TExtRec env1 ident1, TExtRec env2 ident2) -> do
        let commKeys = Map.keysSet env1 `Set.intersection` Map.keysSet env2
            diffKeys1 =  Map.keysSet env1 `Set.difference` Map.keysSet env2
            diffKeys2 =  Map.keysSet env2 `Set.difference` Map.keysSet env1
            commEnv1 = Map.filterWithKey (\x _ -> Set.member x commKeys) env1
            commEnv2 = Map.filterWithKey (\x _ -> Set.member x commKeys) env2
            diffEnv1 = Map.filterWithKey (\x _ -> Set.member x diffKeys1) env1
            diffEnv2 = Map.filterWithKey (\x _ -> Set.member x diffKeys2) env2
        unify (TRec commEnv1) (TRec commEnv2)
        newVarId1 <- getNewTypeVarId
        unify (TVar ident1) (TExtRec diffEnv2 newVarId1)
        newVarId2 <- getNewTypeVarId
        unify (TVar ident2) (TExtRec diffEnv1 newVarId2)
      (TList t1'', TList t2'') -> unify t1'' t2''
      _ -> fail errMsg

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
  ELog exp1 _ exp2  -> inferBinOp exp1 exp2 typeBool
  EEq exp1 _ exp2 -> do
    texp1 <- infer exp1
    texp2 <- infer exp2
    unify texp1 texp2
    return typeBool
  ERel exp1 _ exp2 -> do
    inferBinOp exp1 exp2 typeInt
    return typeBool
  EAdd exp1 _ exp2 -> inferBinOp exp1 exp2 typeInt
  EMul exp1 _ exp2 -> inferBinOp exp1 exp2 typeInt
  ENeg exp1 -> do
    texp <- infer exp1
    unify texp typeBool
    return typeBool
  EVal ident -> do
    ts <- lookupTypeEnv ident
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
  EDot exp1 ident -> do
    texp1 <- infer exp1
    idRecec <- singletonRec ident
    idRececExt <- makeExtRec idRecec
    unify texp1 idRececExt
    getField texp1 ident
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
  _ -> fail $ internalErrMsg

inferLit :: Literal -> InferType Type
inferLit x = case x of
  LTrue      -> return typeBool
  LFalse     -> return typeBool
  LInt _     -> return typeInt
  LRec decls -> do
     oldEnv <- getEnv
     inferedExps <- mapM inferDecl decls
     let idents = map (\x -> case x of
           DFun ident _ _ -> ident
           DVal ident _ -> ident) decls
         typeEnv = Map.fromList (zip idents inferedExps)
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
        return $ TList $ newVar
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
  DFun fname idents exp -> do
    newVar1 <- getNewTypeVar
    newVar2 <- getNewTypeVar
    let fun = TFun newVar1 newVar2
    removeFromEnv fname
    addToEnv fname (TypeScheme [] fun)
    texp1 <- infer (ELam idents exp)
    unify fun texp1
    removeFromEnv fname
    ts <- generalize fun
    addToEnv fname ts
    return ts
  DVal ident exp -> do
    texp <- infer exp
    removeFromEnv ident
    ts <- generalize texp
    addToEnv ident ts
    return ts

checkTypesStmt :: Stmt -> InferType ()
checkTypesStmt stmt = case stmt of
  SExp exp -> void $ infer exp
  SDecl decl -> void $ inferDecl decl

checkTypes' :: Program -> InferType ()
checkTypes' (Prog stmts) = do
  putEnv $ addBuiltInsToTypeEnv emptyEnv
  mapM_ checkTypesStmt stmts

checkTypes :: Program -> Err ()
checkTypes prog =  runInferType $ checkTypes' prog
