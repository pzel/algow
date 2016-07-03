{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
module Main where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set, (\\))
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State

import Debug.Trace

data Exp = EVar String
         | ELit Lit
         | EApp Exp Exp
         | EAbs String Exp
         | ELet String Exp In Exp
         | EOp Op Exp Exp
         deriving (Show)
data In = In deriving (Show)

data Op = And | Or | Add | Mul deriving (Eq,Show)

data Lit = LInt Integer
         | LBool Bool
         deriving (Show)

data Type = TVar String
          | TInt
          | TBool
          | TFun Type Type
         deriving (Eq,Show)

data Scheme = Scheme [String] Type deriving (Show)
type Subst = Map String Type
newtype TypeEnv = TypeEnv (Map String Scheme) deriving (Show)

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
  apply s (Scheme forall t) =
    Scheme forall (apply (foldr Map.delete s forall) t)

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
                         tiSubst :: Subst,
                         tiLogDepth :: Int,
                         tiLog :: [String]
                       } deriving (Show)
type TI a = ErrorT String (ReaderT TIEnv (StateT TIState IO)) a

logDepth :: TI Int
logDepth = tiLogDepth <$> get

putLogEntry :: String -> TI ()
putLogEntry e = get >>= \s-> put s{tiLog= tiLog s ++ [e]}

nested :: TI a -> TI a
nested a = push >> a >>= \res -> pop >> return res
 where pop, push :: TI ()
       pop = get >>= \s-> put s{tiLogDepth= tiLogDepth s - 1}
       push = get >>= \s-> put s{tiLogDepth= tiLogDepth s + 1}

runTI :: TI a -> IO (Either String a, TIState)
runTI t = do
  (res,st) <- runStateT (runReaderT (runErrorT t)
                                    initTIEnv)
              initTIState
  return (res,st)
  where initTIEnv = TIEnv{}
        initTIState = TIState 0 nullSubst 0 []

newTypeVar :: String -> TI Type
newTypeVar prefix = do
  s <- get
  put s{tiSupply= tiSupply s + 1}
  return (TVar (prefix ++ show (tiSupply s)))

instantiate :: Scheme -> TI Type
instantiate (Scheme vars t) = nested $ do
  tr "INST " (Scheme vars t)
  nvars <- mapM (const (newTypeVar "a")) vars
  let s = Map.fromList (zip vars nvars)
  tr "INST new subst" s
  tr "INST returns subst applied to t" (apply s t)
  return (apply s t)

mgu :: Type -> Type -> TI Subst
mgu (TFun l r) (TFun l' r') = nested $ do
  tr "MGU Unifiying "  ((TFun l r),  (TFun l' r'))
  s1 <- mgu l l'
  tr "MGU param types yield subst" s1
  tr "MGU left body with applied param subst:" (apply s1 r)
  tr "MGU right body with applied param subst:" (apply s1 r')
  s2 <- mgu (apply s1 r) (apply s1 r')
  tr "MGU body types yield subst" s2
  tr "MGU returns composed substitutions" (s1 <.> s2)
  return (s1 <.> s2)
mgu (TVar u) t = varBind u t
mgu t (TVar u) = varBind u t
mgu TInt TInt = return nullSubst
mgu TBool TBool = return nullSubst
mgu t1 t2 = throwError $ "types do not unify "
                       ++ show t1 ++ " / " ++ show t2

varBind :: String -> Type -> TI Subst
varBind u t = nested $ tr "VARBIND Binding " (u,t) >> go u t where
 go u t
  | t == TVar u = return nullSubst
  | u `Set.member` (ftv t) = throwError $ u ++ " occurs in ftv of " ++ show t
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
ti env (EAbs n e) = nested $ do
  tr "T-ABS called with" (env, (EAbs n e))
  tv <- newTypeVar "a"
  tr "T-ABS Tv =" tv
  let TypeEnv env' = remove env n
      env'' = TypeEnv (env' `Map.union` (Map.singleton
                                            n (Scheme [] tv)))
  tr "T-ABS shadowed env" env''
  (s1,t1) <- ti env'' e
  tr "T-ABS returns type for Abs:" (TFun (apply s1 tv) t1)
  tr "T-ABS returns subst for Abs:" s1
  return (s1, TFun (apply s1 tv) t1)

ti env (EApp e1 e2) = nested $ do
  tr "T-APP called with" (env, (EApp e1 e2))
  tv <- newTypeVar "a"
  tr "T-APP tv is" tv
  (s1,t1) <- ti env e1
  tr "T-APP e1 types: s1,t1 are" (s1,t1)
  tr "T-APP app s1 env is" (apply s1 env)
  (s2,t2) <- ti (apply s1 env) e2
  tr "T-APP e2 types: s2,t2 are" (s2,t2)
  tr "T-APP app s2 t1" (apply s2 t1)
  tr "T-APP TFun t2 tv" (TFun t2 tv)
  s3 <- mgu (apply s2 t1) (TFun t2 tv)
  tr "T-APP S3" s3
  tr "T-APP returns subst" (s3 <.> s2 <.> s1)
  tr ("T-APP returns " ++show tv ++ ":") (apply s3 tv)

  return (s3 <.> s2 <.> s1, apply s3 tv)

ti env (ELet x e1 In e2) = nested $ do
  tr "T-LET called with" (env,(ELet x e1 In e2))
  (s1,t1) <- ti env e1
  tr "T-LET e1:s,t" (e1,s1,t1)
  let TypeEnv env' = remove env x
      t' = generalize (apply s1 env) t1
      env'' = TypeEnv (Map.insert x t' env')
  tr "T-LET cleaned env" env'
  tr "T-LET generalized t for t1" t'
  tr "T-LET env for e2" env''
  tr "T-LET env for e2/w subst" (apply s1 env'')
  (s2,t2) <- ti (apply s1 env'') e2
  tr "T-LET env final subst,type for e2" (s2,t2)
  tr "T-LET returns subst" (s1 <.> s2)
  tr "T-LET returns type" t2
  return (s1 <.> s2, t2)

ti env (EOp op e1 e2) = nested $ do
  let opType = if op `elem` [Mul,Add] then TInt else TBool
  (s1,t1) <- ti env e1
  (s2,t2) <- ti env e2
  s3 <- mgu opType t1
  s4 <- mgu opType t2
  return (s1 <.> s2 <.> s3 <.> s4 , opType)

typeInference :: Map String Scheme -> Exp -> TI Type
typeInference env e = do
  (s,t) <- ti (TypeEnv env) e
  return (apply s t)

runInference :: Exp -> IO (Either String Type, TIState)
runInference exp = runTI (typeInference (Map.empty) exp)

tr :: (Show a) => String -> a -> TI ()
tr s a = do
  depth <- logDepth
  putLogEntry . (prefix depth ++) . clearQuotes . ((s  ++ " ") ++) . show $ a
 where clearQuotes = filter (/= '"')
       prefix d = take (d*2) (repeat ' ')

exprs :: [Exp]
exprs =
  [
   ELet "outer" (EAbs "x"
                     (ELet "inner" (EAbs "x" (EVar "x"))
                     In (EApp (EVar "inner") (ELit (LInt 2)))) )
      In (EApp (EVar "outer") (ELit (LBool True)))
  ,EApp (EAbs "x" (EOp Mul (EVar "x") (ELit (LInt 2)))) (ELit (LBool True))
  ,EApp (EAbs "x" (EOp Mul (EVar "x") (ELit (LInt 2)))) (ELit (LInt 3))
  ,EApp (EAbs "x" (EOp Mul (EVar "x") (ELit (LInt 2)))) (ELit (LInt 3))
  ,EApp (EAbs "x" (EOp And (EVar "x") (ELit (LBool True)))) (ELit (LBool True))
  ,EApp (EAbs "x" (EOp And (EVar "x") (ELit (LBool True)))) (ELit (LInt 2))
  ,EAbs "x" (EApp (EVar "x") (EVar "x"))
 ]


prettyResult :: (Exp, (Either String Type, TIState)) -> IO ()
prettyResult (e,(t,st)) = do
  putStrLn ("\n\nExpression\n> " ++ show e ++  "\n typed as\n> " ++ show t)
  putStrLn "\nInference log:"
  mapM_ putStrLn (tiLog st)

main = do
  x <- mapM (\e -> runInference e >>= return . (e,) ) exprs
  mapM_ prettyResult x
