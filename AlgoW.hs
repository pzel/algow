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
instantiate (Scheme vars t) = do
  nvars <- mapM (const (newTypeVar "a")) vars
  let s = Map.fromList (zip vars nvars)
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
mgu t1 t2 = throwError $ "types do not unify"
                       ++ show t1 ++ " vs. " ++ show t2

varBind :: String -> Type -> TI Subst
varBind u t = nested $ tr "VARBIND Binding " (u,t) >> go u t where
 go u t
  | t == TVar u = return nullSubst
  | u `Set.member` (ftv t) = throwError $ "occurs: "
                              ++ u ++ " vs " ++ show t
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
  tr "TI called with" (EAbs n e)
  tv <- newTypeVar "abs"
  tr "TI Tv =" tv
  let TypeEnv env' = remove env n
      env'' = TypeEnv (env' `Map.union` (Map.singleton
                                            n (Scheme [] tv)))
  tr "TI shadowed env" env''
  (s1,t1) <- ti env'' e
  tr "TI returns type for Abs:" (TFun (apply s1 tv) t1)
  tr "TI returns subst for Abs:" s1
  return (s1, TFun (apply s1 tv) t1)

ti env (EApp e1 e2) = nested $ do
  tr "TI called with" (env, (EApp e1 e2))
  tv <- newTypeVar "app"
  tr "TI tv is" tv
  (s1,t1) <- ti env e1
  tr "TI e1 types: s1,t1 are" (s1,t1)
  (s2,t2) <- ti (apply s1 env) e2
  tr "TI app s1 env is" (apply s1 env)
  tr "TI e2 types: s2,t2 are" (s2,t2)
  s3 <- mgu (apply s2 t1) (TFun t2 tv)
  tr "TI app s2 t1" (apply s2 t1)
  tr "TI TFun t2 tv" (TFun t2 tv)
  tr "TI S3" s3
  tr "TI returns subst" (s3 <.> s2 <.> s1)
  tr ("TI returns " ++show tv ++ ":") (apply s3 tv)
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

tr :: (Show a) => String -> a -> TI ()
tr s a = do
  depth <- logDepth
  putLogEntry . (prefix depth ++) . clearQuotes . ((s  ++ " ") ++) . show $ a
 where clearQuotes = filter (/= '"')
       prefix d = take d (repeat ' ')

exprs :: [Exp]
exprs =
  [
   EApp (EAbs "x" (EVar "x")) (ELit (LInt 3))

  ]
        -- ELet "id" (EAbs "x" (EVar "x")) (EVar "id")
        -- , ELet "id" (EAbs "x" (EVar "x"))
        --     (EApp (EVar "id") (EVar "id"))
        -- , EApp (EAbs "x" (EVar "x")) (ELit (LInt 2))
        -- ]

prettyResult :: (Exp, (Either String Type, TIState)) -> IO ()
prettyResult (e,(t,st)) = do
  putStrLn ("\nExpression\n> " ++ show e ++  "\n typed as\n> " ++ show t)
  putStrLn "Inference log:"
  mapM_ putStrLn (tiLog st)

main = do
  x <- mapM (\e -> runInference e >>= return . (e,) ) exprs
  mapM_ prettyResult x





