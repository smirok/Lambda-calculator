module LambdaCalculus where

import Text.ParserCombinators.Parsec (
    Parser(..),
    many,
    spaces,
    (<|>),
    sepBy1,
    sepEndBy1,
    char,
    string,
    letter,
    alphaNum,
    runParser)
import Data.List (union, maximumBy)
import Data.Function (on)

type Symb = String 

infixl 4 :@

data Expr = Var Symb
          | Expr :@ Expr
          | Lam Symb Expr
          deriving (Eq)

instance Show Expr where
    showsPrec _ (Var sym)         = showString sym
    showsPrec _ (expr :@ Var sym) = shows expr . showChar ' ' . showString sym
    showsPrec _ (Var sym :@ expr) = showString sym  . showChar ' ' . showChar '(' . shows expr . showChar ')'
    showsPrec _ (Lam sym expr)    = showChar '\\' . showString sym . showString " -> " . shows expr
    showsPrec _ (lTerm :@ rTerm)  = showChar '(' . shows lTerm . showString ") (" . shows rTerm . showChar ')'

instance Read Expr where
  readsPrec _ str = case runParser parseExpr () "" str of
      Right x -> [(x,"")]
      Left _  -> []

freeVars :: Expr -> [Symb]
freeVars (Var sym)        = [sym]  
freeVars (lTerm :@ rTerm) = freeVars lTerm `union` freeVars rTerm
freeVars (Lam sym expr)   = filter (sym /=) $ freeVars expr 

subst :: Symb -> Expr -> Expr -> Expr 
subst var newTerm (Var sym) 
    | sym == var  = newTerm
    | otherwise   = Var sym     
subst var newTerm (lTerm :@ rTerm) = subst var newTerm lTerm :@ subst var newTerm rTerm
subst var newTerm oldTerm@(Lam sym expr) 
    | sym == var                     = oldTerm
    | notElem sym $ freeVars newTerm = Lam sym (subst var newTerm expr)
    | otherwise                      = Lam newSym (subst var newTerm newExpr)
    where
        newSym  = maximumBy (compare `on` length) (freeVars newTerm `union` freeVars expr) ++ "\'"
        newExpr = subst sym (Var newSym) expr

infix 1 `alphaEq`

alphaEq :: Expr -> Expr -> Bool
alphaEq (Var lSym) (Var rSym)               = lSym == rSym
alphaEq (lTerm :@ rTerm) (lTerm' :@ rTerm') = (lTerm `alphaEq` lTerm') && (rTerm `alphaEq` rTerm')
alphaEq (Lam lSym lExpr) (Lam rSym rExpr) 
    | lSym == rSym                  = lExpr `alphaEq` rExpr
    | notElem lSym $ freeVars rExpr = lExpr `alphaEq` subst rSym (Var lSym) rExpr
    | otherwise                     = False
alphaEq _ _ = False


reduceOnce :: Expr -> Maybe Expr
reduceOnce (Lam sym expr :@ term) = Just (subst sym term expr)
reduceOnce (Lam sym m)  = case reduceOnce m of
    Nothing   -> Nothing
    Just expr -> Just (Lam sym expr)
reduceOnce (Var _) = Nothing
reduceOnce (lTerm :@ rTerm) = case reduceOnce lTerm of
    Just x  -> Just (x :@ rTerm)
    Nothing -> case reduceOnce rTerm of
        Nothing -> Nothing
        Just x  -> Just (lTerm :@ x)

nf :: Expr -> Expr 
nf expr = case reduceOnce expr of
    Nothing    -> expr
    Just notNF -> nf notNF

infix 1 `betaEq`

betaEq :: Expr -> Expr -> Bool 
betaEq lExpr rExpr = nf lExpr `betaEq` nf rExpr

parseVariable :: Parser String
parseVariable = spaces >> (:) <$> letter <*> many alphaNum

parseVar :: Parser Expr
parseVar = Var <$> parseVariable    

parseLambda :: Parser Expr
parseLambda = do
    _    <- char '\\' >> spaces
    vars <- sepEndBy1 parseVariable spaces
    _    <- string "->" >> spaces
    expr <- parseExpr
    return $ foldr Lam expr vars

parseBracketsExpr :: Parser Expr
parseBracketsExpr = do
    _ <- char '(' >> spaces
    expr <- parseExpr
    _ <- char ')' >> spaces
    return expr

parseExpr :: Parser Expr
parseExpr = do
    exprs <- sepBy1 (parseBracketsExpr <|> parseLambda <|> parseVar) spaces
    return $ foldl1 (:@) exprs