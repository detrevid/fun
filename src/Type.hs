module Type where

import AbsFun
import ErrM

import qualified Data.Map as Map
import qualified Data.Set as Set

import Control.Monad.State
import Debug.Trace

data Type = TInt
          | TBool
          | TVal Ident
          | TFun Type Type
          deriving (Eq, Ord, Show)

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
lookupSub sub id =
  case Map.lookup id sub of
    Nothing  -> TVal id
    Just t   -> t

lookupTypeEnv :: TypeEnv -> Ident -> Err TypeScheme
lookupTypeEnv env id =
  case Map.lookup id env of
    Nothing  -> Bad $ "Variable " ++ show id ++ "is not bound"
    Just t   -> Ok t

composeSubst :: Subst -> Subst -> Subst
composeSubst sub1 sub2 = Map.union (Map.map (instType sub1) sub2) sub1

ftv :: Type -> Set.Set Ident
ftv t =
  case t of
    TInt       -> Set.empty
    TBool      -> Set.empty
    TVal id    -> Set.singleton id
    TFun t1 t2 -> Set.union (ftv t1) (ftv t2)

ftvScheme :: TypeScheme -> Set.Set Ident
ftvScheme (TypeScheme ids t) =
  Set.difference (ftv t) (Set.fromList ids)

ftvEnv :: TypeEnv -> Set.Set Ident
ftvEnv te =
  Map.foldr (\x y -> Set.union y $ ftvScheme x) Set.empty te

-- instance type
instType :: Subst -> Type -> Type
instType sub t =
  case t of
    TVal id    -> lookupSub sub id
    TFun t1 t2 -> TFun (instType sub t1) (instType sub t2)
    _          -> t

-- instance typeScheme
instTypeScheme :: Subst -> TypeScheme -> TypeScheme
instTypeScheme sub ts =
  case ts of
    TypeScheme ids t -> TypeScheme ids $ instType (foldr Map.delete sub ids) t

instTypeEnv :: Subst -> TypeEnv -> TypeEnv
instTypeEnv sub env = Map.map (instTypeScheme sub) env

unify :: Type -> Type -> Err Subst
unify t1 t2
  | t1 == t2  =  return idSub
  | otherwise =
    case (t1, t2) of
      (TVal id, _)           ->
        if Set.member id $ ftv t2 then Bad "MISTAAAKE!"
                                  else return (Map.singleton id t2)
      (_, TVal id)           ->
        if Set.member id $ ftv t1 then Bad "MISTAAAKE!"
                                  else return (Map.singleton id t1)
      (TFun x y, TFun x' y') -> do
        s1 <- unify x x'
        s2 <- unify (instType s1 y) (instType s1 y')
        return $ composeSubst s1 s2
      (_, _)                 ->  Bad "MISTAAAKE!"

infer :: TypeEnv -> TypeVarSupplier -> Exp -> Err (Type, Subst, TypeVarSupplier)
infer env tvs exp =
  case exp of
    ELet id exp1 exp2  -> do
      (texp1, sub1, tvs') <- infer env tvs exp1
      let env' = Map.delete id env
          ts' = TypeScheme (Set.toList (Set.difference (ftvEnv (instTypeEnv sub1 env)) (ftvEnv env))) texp1
          env'' = Map.insert id ts' env'
        in do
          (texp2, sub2, tvs'') <- infer (instTypeEnv sub1 env'') tvs' exp2
          return (texp2, composeSubst sub2 sub1, tvs'')
    EIf cond exp1 exp2  -> do
      (tcond, sub, tvs') <- infer env tvs cond
      let env' = instTypeEnv sub env in do
        (texp1, sub1, tvs'') <- infer env' tvs' exp1
        (texp2, sub2, tvs''') <- infer (instTypeEnv sub1 env') tvs'' exp2
        sub3          <- unify texp1 texp2
        return (instType sub3 texp2, composeSubst (composeSubst (composeSubst sub3 sub2) sub1) sub, tvs'')
    ELog exp1 logopr exp2  ->
       inferBinBoolOp env tvs exp1 exp2
    EEq exp1 eqopr exp2  ->
      let intInfer = inferBinIntOp env tvs exp1 exp2 in
        case intInfer of
          Bad m                 -> inferBinBoolOp env tvs exp1 exp2
          Ok (texp, sub1, tvs') -> return (TBool, sub1, tvs')
    ERel exp1 relopr exp2  -> do
      (texp, sub1, tvs') <- inferBinIntOp env tvs exp1 exp2
      return (TBool, sub1, tvs')
    EAdd exp1 addopr exp2  -> inferBinIntOp env tvs exp1 exp2
    EMul exp1 mulopr exp2  -> inferBinIntOp env tvs exp1 exp2
    ENeg exp1 -> do
      (texp, sub1, tvs') <- infer env tvs exp1
      sub2 <- unify texp TBool
      return (texp, sub2, tvs')
    EVal id -> do
      ts <- lookupTypeEnv env id
      (ts', tvs') <- instantAll tvs ts
      Ok (ts', idSub, tvs')
    EConst const  -> Ok (inferConst const, idSub, tvs)
    ELam args exp1 ->
      case args of
        h:t ->
          let (newId, tvs') = getNewTypeVar tvs
              newEnv = Map.delete h env
              newEnv' = (Map.union newEnv (Map.singleton h (TypeScheme [] (TVal newId))))
          in do
            (texp1, sub1, tvs'') <- infer newEnv' tvs' $ ELam t exp1
            return (TFun (instType sub1 (TVal newId)) texp1, sub1, tvs'')
        []  ->
          infer env tvs exp1
    EApp exp1 exp2  ->
       let (newId, tvs') = getNewTypeVar tvs in do
       (texp1, sub1, tvs'') <- infer env tvs' exp1
       (texp2, sub2, tvs''') <- infer (instTypeEnv sub1 env) tvs'' exp2
       sub3 <- unify (instType sub2 texp1) (TFun texp2 (TVal newId))
       return (instType sub3 (TVal newId), composeSubst sub3 (composeSubst sub2 sub1), tvs''')

inferConst :: Constant -> Type
inferConst x =
 case x of
   CTrue   -> TBool
   CFalse  -> TBool
   CInt _  -> TInt

inferBinIntOp :: TypeEnv -> TypeVarSupplier -> Exp -> Exp -> Err (Type, Subst, TypeVarSupplier)
inferBinIntOp env tvs exp1 exp2 = do
  (texp1, sub1, tvs') <- infer env tvs exp1
  (texp2, sub2, tvs'') <- infer (instTypeEnv sub1 env) tvs' exp2
  sub3  <- unify (instType sub2 texp1) TInt
  sub4  <- unify (instType sub3 texp2) TInt
  let sub = composeSubst sub4 (composeSubst sub3 (composeSubst sub2 sub1)) in
    return (TInt, sub, tvs'')

inferBinBoolOp :: TypeEnv -> TypeVarSupplier -> Exp -> Exp -> Err (Type, Subst, TypeVarSupplier)
inferBinBoolOp env tvs exp1 exp2 = do
  (texp1, sub1, tvs') <- infer env tvs exp1
  (texp2, sub2, tvs'') <- infer (instTypeEnv sub1 env) tvs' exp2
  sub3  <- unify (instType sub2 texp1) TBool
  sub4  <- unify (instType sub3 texp2) TBool
  let sub = composeSubst sub4 (composeSubst sub3 (composeSubst sub2 sub1)) in
    return (TBool, sub, tvs'')

inferDecl :: TypeEnv -> TypeVarSupplier -> Decl -> Err TypeEnv
inferDecl env tvs decl =
  case decl of
     DFun fname ids exp ->
       let (newId1, tvs') = getNewTypeVar tvs
           (newId2, tvs'') = getNewTypeVar tvs'
           fun = TFun (TVal newId1) (TVal newId2)
           env' = Map.delete fname env
           env'' = Map.insert fname (TypeScheme [newId1, newId2] fun) env'
       in do
         (texp1, sub1, tvs''') <- infer env'' tvs'' (ELam ids exp)
         sub2  <- unify (instType sub1 fun) (trace (show texp1) (texp1))
         return $ instTypeEnv (composeSubst sub2 sub1) env''

checkTypesStmt :: TypeEnv -> Stmt -> Err TypeEnv
checkTypesStmt env stmt =
  case stmt of
    SExp exp  -> case infer env newTypeVarSupplier exp of
      Ok (t, s, tvs) -> trace (show t) (Ok env)
      Bad m -> Bad m
    DExp decl  -> case inferDecl env newTypeVarSupplier decl of
      Ok e ->  Ok e
      Bad m -> Bad m

checkTypes :: Program -> Err TypeEnv
checkTypes x = case x of
  Prog stmts ->
    foldl (\x y -> case x of
      Ok env -> checkTypesStmt env y
      Bad m -> Bad m) (Ok emptyTypeEnv) stmts
