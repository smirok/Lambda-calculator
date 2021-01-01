{-# LANGUAGE FlexibleContexts #-}
module TypeInference where

import Data.List
import Control.Monad.Except
import Control.Monad.State
import LambdaCalculus (
    Symb,
    Expr(..),
    freeVars)

infixr 3 :->

-- Тип
data Type = TVar Symb 
          | Type :-> Type
  deriving (Eq,Show)

-- Контекст
newtype Env = Env [(Symb,Type)]
  deriving (Eq,Show)

-- Подстановка
newtype SubsTy = SubsTy [(Symb, Type)]
  deriving (Eq,Show)

freeTVars :: Type -> [Symb]
freeTVars (TVar sym)        = [sym]
freeTVars (type1 :-> type2) = union (freeTVars type1) (freeTVars type2)

extendEnv :: Env -> Symb -> Type -> Env
extendEnv (Env context) var type' = Env $ (var, type') : context

freeTVarsEnv :: Env -> [Symb]
freeTVarsEnv (Env context) = foldr 
  (\(sym,type') rec -> union (freeTVars $ type') rec)
  []
  context 

appEnv :: (MonadError String m) => Env -> Symb -> m Type
appEnv (Env context) sym = do
  case lookup sym context of
    Nothing -> throwError $ "There is no variable " ++ show sym ++ " in the enviroment."
    Just x  -> return x