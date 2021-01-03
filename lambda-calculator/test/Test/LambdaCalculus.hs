module Test.LambdaCalculus where

import Test.Tasty.HUnit (Assertion, (@?=))
import System.Exit
import LambdaCalculus
import Combinators

unit_freeVars :: Assertion
unit_freeVars = do
    freeVars cK                             @?= []
    freeVars (Var "x")                      @?= ["x"]
    freeVars (Var "x" :@ Var "y")           @?= ["x","y"]
    freeVars (Lam "y" (Var "x" :@ Var "y")) @?= ["x"]

unit_subst :: Assertion
unit_subst = do
    subst "y" (Var "x") (Lam "x" $ (Var "x") :@ (Var "y")) @?= Lam "y'" (Var "y'" :@ Var "x") 
    subst "y" (Var "z") cI                                 @?= Lam "x" (Var "x") 
    subst "y" (Var "x") cI                                 @?= Lam "x'" (Var "x'")

unit_alphaEq :: Assertion
unit_alphaEq = do
    alphaEq (Var "x") (Var "x")                                         @?= True
    alphaEq (Var "x") (Var "y")                                         @?= False
    alphaEq (Lam "x" $ Lam "y" $ Var "x") (Lam "y" $ Lam "x" $ Var "y") @?= True
    alphaEq (Var "x") (Var "x" :@ Var "y")                              @?= False
    alphaEq (Lam "y" $ Var "x") (Lam "x" $ Var "x")                     @?= False

unit_reduceOnce :: Assertion
unit_reduceOnce = do
    reduceOnce (Lam "x" $ Lam "y" $ Var "x")                                @?= Nothing
    reduceOnce (Lam "x" $ Lam "y" $ (Lam "z" $ Var "z") :@ Var "x")         @?= Just (Lam "x" (Lam "y" (Var "x")))
    let omega = Lam "x" $ Var "x" :@ Var "x" in reduceOnce (omega :@ omega) @?=
        Just (Lam "x" (Var "x" :@ Var "x") :@ Lam "x" (Var "x" :@ Var "x"))

unit_nf :: Assertion
unit_nf = do
    alphaEq (nf (fac :@ three)) six     @?= True
    nf six                              @?= six
    nf ((Lam "x" (Var "x")) :@ Var "y") @?= Var "y"

unit_betaEq :: Assertion
unit_betaEq = do
    betaEq (fac :@ three) six                         @?= True
    betaEq ((Lam "x" (Var "x")) :@ Var "y") (Var "y") @?= True

unit_ShowExpr :: Assertion
unit_ShowExpr = do
    show (Lam "x" (Var "x" :@ Var "y")) @?= "\\x -> x y"
    show cY                             @?= "\\f -> (\\z -> f (z z)) (\\z -> f (z z))"

unit_ReadExpr :: Assertion
unit_ReadExpr = do
    (read "\\x1 x2 -> x1 x2 x2" :: Expr) @?= Lam "x1" (Lam "x2" (Var "x1" :@ Var "x2" :@ Var "x2"))
    read (show cY)                       @?= cY