module Type where

import AbsFun
import ErrM

import qualified Data.Map as Map
import qualified Data.Set as Set

import Control.Monad.State
import Debug.Trace

data Type = TInner Inner
          | TVal Ident
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

data TypeVarSupplier = TypeVarSupplier { count :: Int }

getNewTypeVar :: TypeVarSupplier -> (Ident, TypeVarSupplier)
getNewTypeVar tvs =
  (Ident $ ["t" ++ show i | i <- [1..]] !! c, TypeVarSupplier { count = c + 1 })
 where c = count tvs

newTypeVarSupplier :: TypeVarSupplier
newTypeVarSupplier = TypeVarSupplier { count = 0 }

emptyTypeEnv :: TypeEnv
emptyTypeEnv = Map.empty

instantAll :: TypeVarSupplier -> TypeScheme -> Err (Type, TypeVarSupplier)
instantAll tvs (TypeScheme ids t) =
  Ok (t', tvs')
 where
  (ids', tvs') = foldr (\y x -> let (newId, newTS) = getNewTypeVar $ snd x in (newId : fst x, newTS)) ([], tvs) ids
  sub = Map.fromList (zip ids (map TVal ids'))
  t' = instType sub t

idSub :: Subst
idSub = Map.empty

lookupSub :: Subst -> Ident -> Type
lookupSub sub id = case Map.lookup id sub of
    Nothing  -> TVal id
    Just t   -> t

lookupTypeEnv :: TypeEnv -> Ident -> Err TypeScheme
lookupTypeEnv env id = case Map.lookup id env of
  Nothing  -> Bad $ "Variable " ++ show id ++ "is not bound"
  Just t   -> Ok t

composeSubst :: Subst -> Subst -> Subst
composeSubst sub1 sub2 = Map.union (Map.map (instType sub1) sub2) sub1

ftv :: Type -> Set.Set Ident
ftv t = case t of
  TInner _    -> Set.empty
  TVal id    -> Set.singleton id
  TFun t1 t2 -> Set.union (ftv t1) (ftv t2)

ftvScheme :: TypeScheme -> Set.Set Ident
ftvScheme (TypeScheme ids t) = Set.difference (ftv t) (Set.fromList ids)

ftvEnv :: TypeEnv -> Set.Set Ident
ftvEnv te = Map.foldr (\x y -> Set.union y $ ftvScheme x) Set.empty te

-- instance type
instType :: Subst -> Type -> Type
instType sub t = case t of
  TVal id    -> lookupSub sub id
  TFun t1 t2 -> TFun (instType sub t1) (instType sub t2)
  _          -> t

-- instance typeScheme
instTypeScheme :: Subst -> TypeScheme -> TypeScheme
instTypeScheme sub ts = case ts of
  TypeScheme ids t -> TypeScheme ids $ instType (foldr Map.delete sub ids) t

instTypeEnv :: Subst -> TypeEnv -> TypeEnv
instTypeEnv sub env = Map.map (instTypeScheme sub) env

unify :: Type -> Type -> Err Subst
unify t1 t2
  | t1 == t2  =  return idSub
  | otherwise = do
    let errMsg = "Could not unify types: " ++ show t1 ++ show t2
    case (t1, t2) of
      (TVal id, _)           ->
        if Set.member id $ ftv t2 then Bad errMsg
                                  else return (Map.singleton id t2)
      (_, TVal id)           ->
        if Set.member id $ ftv t1 then Bad errMsg
                                  else return (Map.singleton id t1)
      (TFun x y, TFun x' y') -> do
        s1 <- unify x x'
        s2 <- unify (instType s1 y) (instType s1 y')
        return $ composeSubst s1 s2
      (_, _)                 -> Bad errMsg

infer :: TypeEnv -> TypeVarSupplier -> Exp -> Err (Type, Subst, TypeVarSupplier)
infer env tvs exp = case exp of
  ELet id exp1 exp2 -> do
    (texp1, sub1, tvs') <- infer env tvs exp1
    let env' = Map.delete id env
        ts' = TypeScheme (Set.toList (Set.difference (ftvEnv (instTypeEnv sub1 env)) (ftvEnv env))) texp1
        env'' = Map.insert id ts' env'
    (texp2, sub2, tvs'') <- infer (instTypeEnv sub1 env'') tvs' exp2
    return (texp2, composeSubst sub2 sub1, tvs'')
  EIf cond exp1 exp2 -> do
    (tcond, sub, tvs') <- infer env tvs cond
    let env' = instTypeEnv sub env
    (texp1, sub1, tvs'') <- infer env' tvs' exp1
    (texp2, sub2, tvs''') <- infer (instTypeEnv sub1 env') tvs'' exp2
    sub3          <- unify texp1 texp2
    return (instType sub3 texp2, composeSubst (composeSubst (composeSubst sub3 sub2) sub1) sub, tvs'')
  ELog exp1 logopr exp2  -> inferBinOp env tvs exp1 exp2 typeBool
  EEq exp1 eqopr exp2 -> do
    let intInfer = inferBinOp env tvs exp1 exp2 typeInt
    case intInfer of
      Bad m                 -> inferBinOp env tvs exp1 exp2 typeBool
      Ok (texp, sub1, tvs') -> return (typeBool, sub1, tvs')
  ERel exp1 relopr exp2 -> do
    (texp, sub1, tvs') <- inferBinOp env tvs exp1 exp2 typeInt
    return (typeBool, sub1, tvs')
  EAdd exp1 addopr exp2  -> inferBinOp env tvs exp1 exp2 typeInt
  EMul exp1 mulopr exp2  -> inferBinOp env tvs exp1 exp2 typeInt
  ENeg exp1 -> do
    (texp, sub1, tvs') <- infer env tvs exp1
    sub2 <- unify texp typeBool
    return (typeBool, sub2, tvs')
  EVal id -> do
    ts <- lookupTypeEnv env id
    (ts', tvs') <- instantAll tvs ts
    Ok (ts', idSub, tvs')
  EConst const -> Ok (inferConst const, idSub, tvs)
  ELam args exp1 -> case args of
    h:t -> do
      let (newId, tvs') = getNewTypeVar tvs
          newEnv = Map.delete h env
          newEnv' = (Map.union newEnv (Map.singleton h (TypeScheme [] (TVal newId))))
      (texp1, sub1, tvs'') <- infer newEnv' tvs' $ ELam t exp1
      return (TFun (instType sub1 (TVal newId)) texp1, sub1, tvs'')
    []  -> infer env tvs exp1
  EApp exp1 exp2 -> do
    let (newId, tvs') = getNewTypeVar tvs
    (texp1, sub1, tvs'') <- infer env tvs' exp1
    (texp2, sub2, tvs''') <- infer (instTypeEnv sub1 env) tvs'' exp2
    sub3 <- unify (instType sub2 texp1) (TFun texp2 (TVal newId))
    return (instType sub3 (TVal newId), composeSubst sub3 (composeSubst sub2 sub1), tvs''')

inferConst :: Constant -> Type
inferConst x = case x of
 CTrue   -> typeBool
 CFalse  -> typeBool
 CInt _  -> typeInt

inferBinOp :: TypeEnv -> TypeVarSupplier -> Exp -> Exp -> Type -> Err (Type, Subst, TypeVarSupplier)
inferBinOp env tvs exp1 exp2 t = do
  (texp1, sub1, tvs') <- infer env tvs exp1
  (texp2, sub2, tvs'') <- infer (instTypeEnv sub1 env) tvs' exp2
  sub3  <- unify (instType sub2 texp1) t
  sub4  <- unify (instType sub3 texp2) t
  let sub = composeSubst sub4 (composeSubst sub3 (composeSubst sub2 sub1))
  return (t, sub, tvs'')

inferDecl :: TypeEnv -> TypeVarSupplier -> Decl -> Err TypeEnv
inferDecl env tvs decl = case decl of
  DFun fname ids exp -> do
    let (newId1, tvs') = getNewTypeVar tvs
        (newId2, tvs'') = getNewTypeVar tvs'
        fun = TFun (TVal newId1) (TVal newId2)
        env' = Map.delete fname env
        env'' = Map.insert fname (TypeScheme [newId1, newId2] fun) env'
    (texp1, sub1, tvs''') <- infer env'' tvs'' (ELam ids exp)
    sub2  <- unify (instType sub1 fun) (trace (show texp1) (texp1))
    return $ instTypeEnv (composeSubst sub2 sub1) env''

checkTypesStmt :: TypeEnv -> Stmt -> Err TypeEnv
checkTypesStmt env stmt = case stmt of
  SExp exp -> do
    (t, s, tvs) <- infer env newTypeVarSupplier exp
    return $ trace (show t) (env)
  DExp decl -> inferDecl env newTypeVarSupplier decl

checkTypes :: Program -> Err TypeEnv
checkTypes x = case x of
  Prog stmts ->
    foldM (\x y -> checkTypesStmt x y) (emptyTypeEnv) stmts
