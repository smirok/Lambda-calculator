{-# LANGUAGE FlexibleContexts #-}
module TypeInference where

import Data.List
import Control.Monad.Except
import Control.Monad.State
import LambdaCalculus
import Text.ParserCombinators.Parsec

infixr 3 :->

-- Тип
data Type = TVar Symb 
          | Type :-> Type
  deriving (Eq)

instance Show Type where
  showsPrec _ (TVar sym)           = showString sym
  showsPrec _ (TVar sym :-> type') = showString sym . showString " -> " . shows type'
  showsPrec _ (type' :-> TVar sym) = showChar '(' . shows type' . showChar ')' . showString " -> " . showString sym
  showsPrec _ (type1 :-> type2)    = showChar '(' . shows type1 . showChar ')' . showString " -> " . shows type2

-- Контекст
newtype Env = Env [(Symb,Type)]
  deriving (Eq)

instance Show Env where
  showsPrec _ (Env []) = showString "()"
  showsPrec _ (Env env) = 
    showString "(" . 
    foldr 
      (\x rec -> showString (fst x) . showString " : " . shows (snd x) . showString ", " . rec)
      (showString (fst $ last env) . showString " : " . shows (snd $ last env))
      (init env) . 
    showString ")"

-- Подстановка
newtype SubsTy = SubsTy [(Symb, Type)]
  deriving (Eq,Show)

freeTVars :: Type -> [Symb]
freeTVars (TVar sym)        = [sym]
freeTVars (type1 :-> type2) = freeTVars type1 `union` freeTVars type2

extendEnv :: Env -> Symb -> Type -> Env
extendEnv (Env context) var type' = Env $ (var, type') : context

freeTVarsEnv :: Env -> [Symb]
freeTVarsEnv (Env context) = foldr 
  (\(sym,type') rec -> freeTVars type' `union` rec)
  []
  context 

appEnv :: (MonadError String m) => Env -> Symb -> m Type
appEnv (Env context) sym = do
  case lookup sym context of
    Nothing -> throwError $ "There is no variable " ++ show sym ++ " in the enviroment."
    Just x  -> return x

appSubsTy :: SubsTy -> Type -> Type
appSubsTy (SubsTy sub) p@(TVar x) = 
  case lookup x sub of
    Nothing -> p
    Just m  -> m
appSubsTy s (type1 :-> type2) = appSubsTy s type1 :-> appSubsTy s type2    

appSubsEnv :: SubsTy -> Env -> Env
appSubsEnv s (Env context) = Env $ map (fmap $ appSubsTy s) context

getKeys :: SubsTy -> SubsTy -> [Symb]
getKeys (SubsTy xs) (SubsTy ys) = map fst xs `union` map fst ys

makeOneComposition :: Symb -> SubsTy -> SubsTy -> (Symb,Type)
makeOneComposition sym s@(SubsTy xs) (SubsTy ys) = 
  case lookup sym ys of
    Just m  -> (sym, appSubsTy s m)
    Nothing -> case lookup sym xs of
      Just n  -> (sym, n)

makeCompose :: [Symb] -> SubsTy -> SubsTy -> SubsTy
makeCompose [] _ _             = SubsTy []
makeCompose (x:xs) subs1 subs2 = SubsTy $ 
  case makeCompose xs subs1 subs2 of
    SubsTy ys -> makeOneComposition x subs1 subs2 : ys

composeSubsTy :: SubsTy -> SubsTy -> SubsTy
composeSubsTy sub1 sub2 = makeCompose (getKeys sub1 sub2) sub1 sub2

instance Semigroup SubsTy where
  (<>) = composeSubsTy

instance Monoid SubsTy where
  mempty  = SubsTy []
  mappend = composeSubsTy

unify :: MonadError String m => Type -> Type -> m SubsTy
unify (TVar a) (TVar b) 
  | a == b    = return $ SubsTy []
  | otherwise = return $ SubsTy [(a,TVar b)]
unify (TVar a) type' 
  | a `elem` freeTVars type' = throwError $ "Can't unify (" ++ show (TVar a) ++ ") with (" ++ show type' ++ ")!"
  | otherwise                = return $ SubsTy [(a,type')]
unify type' t@(TVar _) = unify t type'
unify (t1 :-> t2) (s1 :-> s2) = do
  u2 <- unify t2 s2
  u1 <- unify (appSubsTy u2 t1) (appSubsTy u2 s1)
  return $ u1 <> u2

equations :: MonadError String m => Env -> Expr -> Type -> m [(Type, Type)]
equations ctxt expr t = evalStateT (equations' ctxt expr t) (-1)
  where
    equations' :: MonadError String m => Env -> Expr -> Type -> StateT Int m [(Type,Type)]
    equations' context (Var sym) type' = do
      new_type <- appEnv context sym
      return [(type', new_type)]
    equations' context (expr1 :@ expr2) type' = do
      new_var <- getNewVar
      ans1 <- equations' context expr1 (new_var :-> type')
      ans2 <- equations' context expr2 new_var
      return $ union ans1 ans2
    equations' context (Lam sym expr) type' = do 
      new <- getNewVar
      new'<- getNewVar
      ans1 <- equations' (extendEnv context sym new) expr new'
      return $ union ans1 [(new :-> new', type')]
    getNewVar :: MonadError String m => StateT Int m Type
    getNewVar = do
      modify (+ 1)
      s <- get
      return $ TVar ('t':show s)

getContext :: Expr -> Env
getContext expr = Env $ zipWith (curry $ fmap TVar) arr (map (\x -> 'a':show x) [0..length arr]) where
  arr = freeVars expr

foldEquations :: [(Type,Type)] -> (Type, Type)
foldEquations = foldr1 (\(x,y) (xrec,yrec) -> (x :-> xrec, y :-> yrec))

principlePair :: (MonadError String m) =>  Expr -> m (Env,Type)
principlePair expr = do
  system       <- equations (getContext expr) expr (TVar "b")
  main_unifier <- uncurry unify (foldEquations system)
  return (appSubsEnv main_unifier (getContext expr), appSubsTy main_unifier (TVar "b"))

getType :: String -> String
getType str = case runParser parseExpr () "" str of
  Left err   -> show err
  Right expr -> case runExcept (principlePair expr) of
    Left err           -> "Typecheck error : " ++ show err
    Right (env, type') -> show env ++ " => " ++ show type'