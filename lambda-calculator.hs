{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}

import Data.List
import Control.Arrow
import Data.Array.Base
import Data.Array.IO
import Data.Array.Unboxed

type Symb = String 
infixl 2 :@
infix 1 `alphaEq`
infix 1 `betaEq`

data Expr = Var Symb
          | Expr :@ Expr
          | Lam Symb Expr
          deriving Eq


instance Show Expr where
    --show :: Expr -> String  
    show (Var a) = a
    show (m1:@m2) = "(" ++ show m1 ++ ") (" ++ show m2 ++ ")"
    show (Lam a m) = "(\\" ++ a ++" -> " ++ show m ++ ")"


getCloseBracketsId :: String -> Array Int Int
getCloseBracketsId str = listArray (0,n-1) (fun (n-1) (reverse str) [])
    where n = length str
          fun :: Int -> String -> [Int] -> [Int]
          fun _ [] _ = []
          fun i (c:str) stack 
            | c == '('  = fun (i-1) str (drop 1 stack) ++ [head stack]
            | c == ')'  = fun (i-1) str (i:stack) ++ [0]
            | otherwise = fun (i-1) str stack ++ [0]

getOpenBracketsId :: String -> Array Int Int 
getOpenBracketsId str = listArray (0,n-1) (fun 0 str [])
    where n = length str
          fun :: Int -> String -> [Int] -> [Int]
          fun _ [] _ = []
          fun i (c:str) stack 
            | c == '('  = 0 : (fun (i+1) str (i:stack))
            | c == ')'  = (head stack) : (fun (i+1) str (drop 1 stack))
            | otherwise = 0 : (fun (i+1) str stack)
                      
readWhileArrow :: String -> (String,[String])
readWhileArrow (c:str) = case c of
    '-'       -> (drop 2 str, [])
    ' '       -> second ("":) $ readWhileArrow str 
    otherwise -> second fun $ readWhileArrow str
        where fun (x:xs) = (c:x):xs
              fun [] = [c:[]]

readWhileSpace :: Int -> String -> (String,String)
readWhileSpace 0 _ = ([],[])
readWhileSpace _ [] = ([],[])
readWhileSpace ost (c:str) = case c of
    ' '       -> (str, [])
    otherwise -> second (c:) $ readWhileSpace (ost-1) str

getAllImplicants :: Int -> String -> (String, [String])
getAllImplicants ct str = case readWhileSpace ct str of 
    (ost,[]) -> (ost, []) 
    (suf,imp) -> second (imp:) $ getAllImplicants (ct-sawCt) suf
        where sawCt = (length str) - (length suf) 


deleteBadSpaces' :: Char -> Char -> String -> String 
deleteBadSpaces' bad _ [] = []
deleteBadSpaces' bad lst (c:str) 
    | c==' ' = if lst == bad then deleteBadSpaces' bad c str else c : deleteBadSpaces' bad c str
    | otherwise = c : deleteBadSpaces' bad c str

lexParser :: String -> [String] 
lexParser str = let ~[(f,s)] = lex str in case (f,s) of 
    (f,"") -> [f] 
    otherwise -> f : lexParser s

lexSuperParser :: [String] -> [String]
lexSuperParser [] = []
lexSuperParser (x:xs)
    | head x == '(' = case rhead x of 
                        ')' -> x : lexSuperParser xs
                        otherwise -> lexSuperParser $ (x++" "++next):xs'
                            where x' = x++"2"
                                  (next:xs') = xs 
    | otherwise = x : lexSuperParser xs

deleteBadSpaces:: String -> String 
deleteBadSpaces str = reverse . deleteBadSpaces' ')' '$' . reverse $ deleteBadSpaces' '\\' '$' $ deleteBadSpaces' '(' '$' $ deleteBadSpaces' ' ' '$' str

lexUberSuperParser :: String -> [String]
lexUberSuperParser s = map deleteBadSpaces $ lexSuperParser . lexParser . deleteBadSpaces $ s

deleteSuf k = reverse . drop k . reverse
rhead = head . reverse

instance Read Expr where
    --readsPrec :: Int -> String -> [(Expr,String)]
    readsPrec _ str = [(fun (n-1) 0 (reverse . deleteBadSpaces $ str),"")]
        where openBracketsId = getOpenBracketsId str
              exprComp :: Expr -> Expr -> Expr 
              exprComp pref cur = pref :@ cur

              varComp :: Expr -> String -> Expr 
              varComp pref cur = pref :@ Var cur

              joinExpr :: [Expr] -> Expr 
              joinExpr exprs = foldl exprComp (head exprs) (drop 1 exprs)              
                            
              n = length str
              fun :: Int -> Int -> String -> Expr
              fun i l ful@(c:str) = case (head $ reverse ful) of 
                    '\\' -> foldr lamComp (fun i (i-(length suf)+1) (reverse suf)) bounds
                        where rev = drop 1 $ reverse ful
                              (suf,bounds) =  readWhileArrow rev
                              sufLen = length suf
                              -- [l,i] -> [l][l+1, l+(length suf)-1][l+(length suf), i]
                              -- [\\][... -> ....]                                    
                              lamComp :: String -> Expr -> Expr
                              lamComp cur suf = Lam cur suf     
                                                        
                    otherwise -> case c of
                        ')' -> if (l'-3)>=l then fun ( (l'-3)) ( l) ( drop (r'-l'+1+2) str) :@ fun r' l' (deleteSuf (l'-l) str) else fun r' l' d1 
                            where l' = (openBracketsId ! i) + 1 
                                  r' = i - 1
                                  d1 = (deleteSuf 1 str)   
                                  -- [l,i] -> [l,l'-3] [ ] [(] [l',r'] [)]
                        otherwise -> snd $ foldl advanceExprComp (makeExprOrVar (l,headExp)) (drop 1 exprs)
                            where rev = reverse ful 
                                  exprs = lexUberSuperParser rev 
                                  headExp = head exprs

                                  makeExprOrVar :: (Int, String) -> (Int, Expr) 
                                  makeExprOrVar (lf,ful@('(':ost)) = (lf+(length ful), fun (lf+(length ful)-1) lf $ reverse ful)
                                  makeExprOrVar (lf,s) = (lf+(length s), Var s)

                                  advanceExprComp :: (Int, Expr) -> String -> (Int, Expr)
                                  advanceExprComp (lf, expr) str = second (expr :@ ) $ makeExprOrVar (lf,str)

betaEq :: Expr -> Expr -> Bool 
betaEq a b = nf a `alphaEq` nf b

nf :: Expr -> Expr 
nf m = case reduceOnce m of 
    Just m' -> nf m' 
    Nothing -> m

reduceOnce :: Expr -> Maybe Expr
reduceOnce (Var a) = Nothing  
reduceOnce (Lam a m) = case reduceOnce m of 
    Just m' -> Just $ Lam a m'
    Nothing -> Nothing
reduceOnce ((Lam a m1) :@ m2) = Just $ subst a m2 m1
reduceOnce (m1 :@ m2) = case (reduceOnce m1, reduceOnce m2) of
    (Just m1', _)       -> Just $ m1' :@ m2 
    (Nothing, Just m2') -> Just $ m1 :@ m2' 
    (Nothing, Nothing)  -> Nothing

alphaEq :: Expr -> Expr -> Bool
alphaEq a b = case (a,b) of
    (Var a, Var b)       -> a == b
    (a1 :@ a2, b1 :@ b2) -> alphaEq a1 b1 && alphaEq a2 b2
    (Lam a am, Lam b bm) -> if a==b then 
                                alphaEq am bm 
                            else    
                                case find (==a) (freeVars bm) of 
                                    Nothing   -> alphaEq am $ subst b (Var a) bm
                                    otherwise -> False
    otherwise            -> False

freeVars :: Expr -> [Symb]
freeVars (Var a)    = [a]
freeVars (m1 :@ m2) = (freeVars m1) ++ (freeVars m2)
freeVars (Lam a m)  = delete a $ freeVars m

subst :: Symb -> Expr -> Expr -> Expr 
subst v n (Var m) 
    | v == m    = n 
    | otherwise = Var m
subst v n (m1 :@ m2) = subst v n m1 :@ subst v n m2
subst v n (Lam bound m)
    | v == bound = Lam bound m
    | otherwise  = do
        let fvN = freeVars m 
        case find (==v) fvN of 
                Nothing -> Lam bound $ subst v n m
                otherwise -> Lam newBound $ subst v n $ subst bound (Var newBound) m
                    where newBound = let ct = foldr (\el pref -> pref `max` length el) 0 $ freeVars n ++ freeVars m 
                                        in bound ++ replicate ct '\''