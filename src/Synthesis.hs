{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE UnicodeSyntax #-}

module Synthesis where

import Data.List (elemIndices, intersect)
import qualified Data.Sequence as S
import Data.Sequence ((><), (|>), (<|))

import GToffoli (GToffoli(GToffoli))
import Circuits (OP)
import Value (Var,fromInt)

------------------------------------------------------------------------------
-- Synthesis algorithm from https://msoeken.github.io/papers/2016_rc_1.pdf

-- Simple helpers

viewL :: [a] -> ([a],a)
viewL xs = (init xs, last xs)

-- negate bit i 

notI :: Int -> [Bool] -> [Bool]
notI i as = xs ++ (not y : ys)
  where (xs,y:ys) = splitAt i as

notIs :: [Bool] -> [Int] -> [Bool]
notIs = foldr notI

allBools :: Int -> [[Bool]]
allBools 0 = [[]]
allBools n = map (False :) bs ++ map (True :) bs
  where bs = allBools (n-1)

------------------------------------------------------------------------------
-- Algorithm

-- Core step of algorithm
-- Take two bit sequences x and y and return GToffoli gates to convert x to y
-- without disturbing any bit sequence that is lexicographically smaller than x

synthesisStep :: [Var s v] -> [Bool] -> [Bool] -> (OP s v, [Bool] -> [Bool])
synthesisStep vars xbools ybools
  | xbools == ybools = (S.empty, id)
  | otherwise =
  let
    x0 = elemIndices False xbools
    x1 = elemIndices True  xbools
    y0 = elemIndices False ybools
    y1 = elemIndices True  ybools
    x0y1 = x0 `intersect` y1
    x1y0 = x1 `intersect` y0
    f01 xs = if and [ xs !! k | k <- x1] then notIs xs x0y1 else xs
    f10 xs = if and [ xs !! k | k <- x0] then notIs xs x1y0 else xs
    toff01 = [ GToffoli
               (replicate (length x1) True)
               [vars !! k | k <- x1]
               (vars !! i)
             | i <- x0y1
             ]
    toff10 = [ GToffoli
               (replicate (length x0) True)
               [vars !! k | k <- x0]
               (vars !! i)
             | i <- x1y0
             ]
  in (S.fromList (toff01 ++ toff10), f01 . f10)

-- -- Initialize; repeat synthesis; extract circuit

synthesisLoop :: [Var s v] -> OP s v -> ([Bool] -> [Bool]) -> [[Bool]] -> OP s v
synthesisLoop _ circ _ [] = circ
synthesisLoop xs circ f (xbools : rest) =
  let ybools = f xbools
      (circg,g) = synthesisStep xs xbools ybools
  in synthesisLoop xs (circg >< circ) (g . f) rest

synthesis :: Int -> [Var s v] -> ([Bool] -> [Bool]) -> OP s v
synthesis n xs f = synthesisLoop xs S.empty f (allBools n)

------------------------------------------------------------------------------
-- Generate all balanced function (2^n -> 2)

subsets :: [a] -> [[a]]
subsets [] = [[]]
subsets (a:as) = map (a :) ss ++ ss
  where ss = subsets as

allFuns :: Int -> [[Bool] -> Bool]
allFuns n = [(`elem` ts) | ts <- maptoT ]
  where maptoT = subsets (allBools n)

allBalancedFuns :: Int -> [[Bool] -> Bool]
allBalancedFuns n = [(`elem` ts) | ts <- maptoT, length ts == bigN `div` 2 ]
  where bigN = 2 ^ n
        maptoT = subsets (allBools n)

{--
number of balanced functions

n=0     1
n=1     2
n=2     6
n=3    70
n=4 12870

--}
------------------------------------------------------------------------------
-- Special synthesis for Grover functions that are guaranteed to have
-- just one entry u such thaat f(u) = 1

synthesisGrover :: Int -> [Var s v] -> Integer -> OP s v
synthesisGrover n (viewL -> (xs,y)) u =
  S.singleton $ GToffoli (fromInt n u) xs y

--------------------------------------------------------------------------------

-- synthesis :: Int → [Var s v] → [Bool → Bool] → OP s v
-- synthesis n xs f =
f :: [Bool] -> [Bool]
f [False,False] = [True]   -- 1
f [False,True]  = [False]  -- 0
f [True,False]  = [True]   -- 1
f [True,True]   = [True]   -- 1

synthesisNew :: Int -> [Var s v] -> ([Bool] -> [Bool]) -> OP s v
synthesisNew n xs f = synthesisHelper xs (allBools n) (getC n f)

synthesisHelper :: [Var s v] -> [[Bool]] -> [Bool] -> OP s v
synthesisHelper xs bs c = generateCircuit (getANF c bs) xs

generateCircuit :: [[Bool]] -> [Var s v] -> OP s v
generateCircuit []      _ = S.empty
generateCircuit (b:bs) xs = S.singleton (GToffoli b xs (whichX xs b)) ><  generateCircuit bs xs

whichX :: [Var s v] -> [Bool] -> (Var s v)
whichX (x:xs) (b:bs) = if b
                       then x
                       else whichX xs bs

getANF :: [Bool] -> [[Bool]] -> [[Bool]]
getANF []     _      = []
getANF _      []     = []
getANF (c:cs) (b:bs) = if c
                       then b : getANF cs bs
                       else getANF cs bs

-- get c s.t T.c = vf
getC ∷ Int → ([Bool] → [Bool]) → [Bool]
getC n f = ntob $ getCHelper (generateT (allBools n) (allBools n)) (getVf f (allBools n))

getVf :: ([Bool] -> [Bool]) -> [[Bool]] -> [Bool]
getVf _ []     = []
getVf f (x:xs) = f x ++ getVf f xs

getCHelper :: [[Bool]] -> [Bool] -> [Int]
getCHelper []     _  = []
getCHelper (t:ts) vs = mod (rc (bton t) (bton vs)) 2 : getCHelper ts vs

rc :: [Int] -> [Int] -> Int
rc [] _ = 0
rc (t:ts) (v:vs) = (t * v) + rc ts vs

bton :: [Bool] -> [Int]
bton []     = []
bton (x:xs) = if x then 1 : bton xs
                   else 0 : bton xs

ntob :: [Int] -> [Bool]
ntob []     = []
ntob (x:xs) = if x == 1
              then True : ntob xs
              else False : ntob xs

generateT :: [[Bool]] -> [[Bool]] -> [[Bool]]
generateT []     [] = [[]]
generateT []     _  = [[]]
generateT _      [] = [[]]
generateT (x:xs) u  = dotProduct x u : generateT xs u

dotProduct :: [Bool] -> [[Bool]] -> [Bool]
dotProduct _ []     = []
dotProduct x (u:us) = and (xi 0 x (ones u 0)) : dotProduct x us

ones :: [Bool] -> Int -> [Int]
ones  []    _   = []
ones (u:us) idx = if u
                  then idx : ones us (idx + 1)
                  else ones us (idx + 1)

xi :: Int -> [Bool] -> [Int] -> [Bool]
xi _   []     _    = []
xi idx (x:xs) ones = if idx `elem` ones
                     then x : xi (idx + 1) xs ones
                     else xi (idx + 1) xs ones

-- applying the isomorphism Φ to f to get ANF
-- represent the ANF in terms of GToffili
