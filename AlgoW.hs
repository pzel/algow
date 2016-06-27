module Main where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set, (\\))
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State

import qualified Text.PrettyPrint as PP


data Exp = EVar String
         | ELit Lit
         | EApp Exp Exp
         | EAbs String Exp
         | ELet String Exp Exp
         deriving (Eq,Ord,Show)

data Lit = LInt Integer
         | LBool Bool
         deriving (Eq,Ord,Show)

data Type = TVar String
          | TInt
          | TBool
          | TFun Type Type
         deriving (Eq,Ord,Show)

data Scheme = Scheme [String] Type -- ∀ᾱ.τ
type Subst = Map String Type
newtype TypeEnv = TypeEnv (Map String Scheme)

class Types a where
  ftv :: a -> Set String
  apply :: Subst -> a -> a

instance Types Type where
  ftv (TVar n) = Set.singleton n
  ftv TInt = Set.empty
  ftv TBool = Set.empty
  ftv (TFun t1 t2) = ftv t1 `Set.union` ftv t2

  apply s (TVar n) = case Map.lookup n s of
                       Nothing -> TVar n
                       (Just t) -> t
  apply s (TFun t1 t2) = TFun (apply s t1) (apply s t2)
  apply s t = t

instance Types Scheme where
  ftv (Scheme forall t) = (ftv t) \\ (Set.fromList forall)
  apply s (Scheme forall t) = Scheme forall (apply (foldr Map.delete s forall) t)

instance Types a => Types [a] where
  ftv l = foldr Set.union Set.empty (map ftv l)
  apply s = map (apply s)

instance Types TypeEnv where
  ftv (TypeEnv env) = ftv (Map.elems env)
  apply s (TypeEnv env) = TypeEnv (Map.map (apply s) env)

nullSubst :: Subst
nullSubst = Map.empty

infixl <.>
(<.>) :: Subst -> Subst -> Subst
s1 <.> s2 = (Map.map (apply s1) s2) `Map.union` s1

remove :: TypeEnv -> String -> TypeEnv
remove (TypeEnv env) var = TypeEnv (Map.delete var env)

generalize :: TypeEnv -> Type -> Scheme
generalize env t = Scheme vars t
  where vars = Set.toList ((ftv t) \\ (ftv env))


data TIEnv = TIEnv {}
data TIState = TIState { tiSupply :: Int,
                         tiSubst :: Subst} deriving (Show)
type TI a = ErrorT String (ReaderT TIEnv (StateT TIState IO)) a

runTI :: TI a -> IO (Either String a, TIState)
runTI t = do
  (res,st) <- runStateT (runReaderT (runErrorT t) initTIEnv) initTIState
  return (res,st)
  where initTIEnv = TIEnv{}
        initTIState = TIState 0 nullSubst

newTypeVar :: String -> TI Type
newTypeVar prefix = do
  s <- get
  put s{tiSupply= tiSupply s + 1}
  return (TVar (prefix ++ show (tiSupply s)))

instantiate :: Scheme -> TI Type
instantiate (Scheme vars t) = do
  nvars <- mapM (const (newTypeVar "a")) vars
  let s = Map.fromList (zip vars nvars)
  return (apply s t)

mgu :: Type -> Type -> TI Subst
mgu (TFun l r) (TFun l' r') = do
  s1 <- mgu l l'
  s2 <- mgu (apply s1 r) (apply s1 r')
  return (s1 <.> s2)
mgu (TVar u) t = varBind u t
mgu t (TVar u) = varBind u t
mgu TInt TInt = return nullSubst
mgu TBool TBool = return nullSubst
mgu t1 t2 = throwError $ "types do not unify " ++ show t1 ++ " vs. " ++ show t2

varBind :: String -> Type -> TI Subst
varBind u t
  | t == TVar u = return nullSubst
  | u `Set.member` (ftv t) = throwError $ "occurs: " ++ u ++ " vs " ++ show t
  | otherwise = return $ Map.singleton u t

tiLit :: TypeEnv -> Lit -> TI (Subst,Type)
tiLit _ (LInt _) = return (nullSubst, TInt)
tiLit _ (LBool _) = return (nullSubst, TBool)

ti :: TypeEnv -> Exp -> TI (Subst, Type)
ti (TypeEnv env) (EVar n) =
  case Map.lookup n env of
    Nothing -> throwError $ "unbound variable" ++ n
    (Just sigma) -> instantiate sigma >>= \t -> return (nullSubst, t)
ti env (ELit l) = tiLit env l
ti env (EAbs n e) = do
  tv <- newTypeVar "a"
  let TypeEnv env' = remove env n
      env'' = TypeEnv (env' `Map.union` (Map.singleton n (Scheme [] tv)))
  (s1,t1) <- ti env'' e
  return (s1, TFun (apply s1 tv) t1)
ti env (EApp e1 e2) = do
  tv <- newTypeVar "a"
  (s1,t1) <- ti env e1
  (s2,t2) <- ti (apply s1 env) e2
  s3 <- mgu (apply s2 t1) (TFun t2 tv)
  return (s3 <.> s2 <.> s1, apply s3 tv)
ti env (ELet x e1 e2) = do
  (s1,t1) <- ti env e1
  let TypeEnv env' = remove env x
      t' = generalize (apply s1 env) t1
      env'' = TypeEnv (Map.insert x t' env')
  (s2,t2) <- ti (apply s1 env'') e2
  return (s1 <.> s2, t2)

typeInference :: Map String Scheme -> Exp -> TI Type
typeInference env e = do
  (s,t) <- ti (TypeEnv env) e
  return (apply s t)

runInference :: Exp -> IO (Either String Type, TIState)
runInference exp = runTI (typeInference (Map.empty) exp)

exprs :: [Exp]
exprs = [ ELet "id" (EAbs "x" (EVar "x")) (EVar "id")
        , ELet "id" (EAbs "x" (EVar "x")) (EApp (EVar "id") (EVar "id"))
        , EApp (EAbs "x" (EVar "x")) (ELit (LInt 2))
        ]
main = do
  x <- mapM runInference exprs
  putStrLn (show (map fst x))
