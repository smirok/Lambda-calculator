module Test.TypeInference where

import Test.Tasty.HUnit (Assertion, (@?=))
import TypeInference
import LambdaCalculus
import Combinators

unit_freeTVars :: Assertion
unit_freeTVars = do
    freeTVars (TVar "a")              @?= ["a"]
    freeTVars (TVar "a" :-> TVar "b") @?= ["a","b"]

unit_extendEnv :: Assertion
unit_extendEnv = do
    extendEnv (Env []) "x" (TVar "a" :-> TVar "b")   @?= Env [("x", TVar "a" :-> TVar "b")]
    extendEnv (Env [("a", TVar "b")]) "x" (TVar "y") @?= Env [("x", TVar "y"), ("a", TVar "b")]

unit_freeTVarsEnv :: Assertion
unit_freeTVarsEnv = do
    freeTVarsEnv (Env [("x", TVar "a" :-> TVar "b")])                 @?= ["a","b"]
    freeTVarsEnv (Env [("x", TVar "a" :-> TVar "b"),("y", TVar "c")]) @?= ["a","b","c"]

unit_appEnv :: Assertion
unit_appEnv = do
    appEnv (Env [("x", TVar "a" :-> TVar "b"), ("y", TVar "c")]) "x" @?= Right (TVar "a" :-> TVar "b")
    appEnv (Env [("x", TVar "a" :-> TVar "b"), ("y", TVar "c")]) "y" @?= Right (TVar "c")
    appEnv (Env [("x", TVar "a" :-> TVar "b"), ("y", TVar "c")]) "z" @?= Left "There is no variable \"z\" in the enviroment."

unit_appSubsTy :: Assertion
unit_appSubsTy = do
    appSubsTy (SubsTy [("a", TVar "b")]) (TVar "a" :-> TVar "a")                               @?=
        TVar "b" :-> TVar "b"
    appSubsTy (SubsTy [("a", TVar "b"), ("b", TVar "c")]) (TVar "b" :-> TVar "d" :-> TVar "a") @?=
        TVar "c" :-> TVar "d" :-> TVar "b"

unit_appSubsEnv :: Assertion
unit_appSubsEnv = do
    appSubsEnv (SubsTy [("a", TVar "b")]) (Env [("x", TVar "a" :-> TVar "b")])                                   @?=
        Env [("x", TVar "b" :-> TVar "b")]
    appSubsEnv (SubsTy [("a", TVar "b"), ("c", TVar "d")]) (Env [("x", TVar "a" :-> TVar "b"), ("y", TVar "c")]) @?=
        Env [("x", TVar "b" :-> TVar "b"), ("y", TVar "d")]

unit_composeSubsTy :: Assertion
unit_composeSubsTy = do
    composeSubsTy (SubsTy [("a", TVar "b")]) (SubsTy [("b", TVar "a")]) @?= SubsTy [("a", TVar "b"),("b", TVar "b")]
    composeSubsTy (SubsTy [("a", TVar "b")]) (SubsTy [("c", TVar "d")]) @?= SubsTy [("a", TVar "b"),("c", TVar "d")]

unit_unify :: Assertion
unit_unify = do
    unify (TVar "a" :-> TVar "b") (TVar "c")              @?= Right (SubsTy [("c",TVar "a" :-> TVar "b")])
    unify (TVar "a" :-> TVar "b") (TVar "c" :-> TVar "d") @?= Right (SubsTy [("a",TVar "c"),("b",TVar "d")])
    unify (TVar "a") (TVar "a" :-> TVar "a")              @?=
        Left "Can't unify (a) with (a -> a)!"

unit_equations :: Assertion
unit_equations = do
    equations (Env [("x",TVar "a" :-> TVar "b")]) (Lam "y" $ Var "x") (TVar "o") @?=
        Right [(TVar "t1",TVar "a" :-> TVar "b"),(TVar "t0" :-> TVar "t1",TVar "o")]
    equations (Env []) (Lam "y" $ Var "x") (TVar "o")                            @?=
        Left "There is no variable \"x\" in the enviroment."

unit_principlePair :: Assertion
unit_principlePair = do
    principlePair (Var "x")                     @?= Right (Env [("x",TVar "a0")],TVar "a0")
    principlePair (Var "f" :@ Var "x")          @?= Right (Env [("f",TVar "a1" :-> TVar "b"),("x",TVar "a1")],TVar "b")
    principlePair (Lam "x" $ Lam "y" $ Var "y") @?= Right (Env [],TVar "t0" :-> (TVar "t2" :-> TVar "t2"))
    principlePair (Var "x" :@ Var "x")          @?= Left "Can't unify (a0) with (a0 -> b)!"