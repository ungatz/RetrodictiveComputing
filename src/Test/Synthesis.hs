{-# LANGUAGE ViewPatterns #-}

module Test.Synthesis where
import Control.Monad.ST (runST)
import Data.STRef (newSTRef)

import Value (Var, Value(..), newVar, newVars, fromInt)
import FormulaRepr (FormulaRepr(..))
import Circuits (showOP)
import Synthesis (synthesis, synthesisNew)

----------------------------------------------------------------------------------------
-- Some test cases of the synthesis algorithm


-- Let B = {0, 1} the set of the Boolean values and B the set of functions from
-- f: Bⁿ → B
-- For the old synthesis algorithm the functions had to be reversible.
-- But this algorithm generates circuit for any f that the oracle implements?

viewL :: [a] -> ([a],a)
viewL xs = (init xs, last xs)

uf :: ([Bool] -> Bool) -> ([Bool] -> [Bool])
uf f (viewL -> (xs,y)) = xs ++ [f xs /= y]

notGateTest :: IO ()
notGateTest = putStrLn $ runST $ do
  x0 <- newSTRef "x0"
  x1 <- newSTRef "x1"
  let op = synthesis 2 [x1,x0] (uf f)
  showOP op
  where f [True] = False
        f [False] = True

notGateTestN :: IO ()
notGateTestN = putStrLn $ runST $ do
  x0 <- newSTRef "x0"
  x1 <- newSTRef "x1"
  let op = synthesisNew 1 [x1,x0] f
  showOP op
  where f [True] = [False]
        f [False] = [True]

test1 :: IO ()
test1 = putStrLn $ runST $ do
  x0 <- newSTRef "x0"
  x1 <- newSTRef "x1"
  let op = synthesis 2 [x1,x0] (\[a,b] -> [a,a/=b])
  showOP op

test1N :: IO ()
test1N = putStrLn $ runST $ do
  x0 <- newSTRef "x0"
  x1 <- newSTRef "x1"
  let op = synthesisNew 1 [x1,x0] (\[a] -> [a])
  showOP op

test2 :: IO ()
test2 = putStrLn $ runST $ do
  x0 <- newSTRef "x0"
  x1 <- newSTRef "x1"
  x2 <- newSTRef "x2"
  let op = synthesis 3 [x2,x1,x0] (\[a,b,c] -> [a,b,(a&&b)/=c])
  showOP op

test2N :: IO ()
test2N = putStrLn $ runST $ do
  x0 <- newSTRef "x0"
  x1 <- newSTRef "x1"
  x2 <- newSTRef "x2"
  let op = synthesisNew 2 [x2,x1,x0] (\[a,b] -> [(a&&b)])
  showOP op

testNew :: IO ()
testNew = putStrLn $ runST $ do
  x0 <- newSTRef "x0"
  x1 <- newSTRef "x1"
  x2 <- newSTRef "x2"
  x3 <- newSTRef "x3"
  let op = synthesisNew 3 [x3,x2,x1,x0] g
  showOP op
  where g [False,False,False] = [False]
        g [False,False,True]  = [False]
        g [False,True,False]  = [True]
        g [False,True,True]   = [False]
        g [True,False,False]  = [True]
        g [True,False,True]   = [False]
        g [True,True,False]   = [False]
        g [True,True,True]    = [True]

testOld :: IO ()
testOld = putStrLn $ runST $ do
  x0 <- newSTRef "x0"
  x1 <- newSTRef "x1"
  x2 <- newSTRef "x2"
  x3 <- newSTRef "x3"
  let op = synthesis 4 [x3,x2,x1,x0] (uf g)
  showOP op
  where g [False,False,False] = False
        g [False,False,True]  = False
        g [False,True,False]  = True
        g [False,True,True]   = False
        g [True,False,False]  = True
        g [True,False,True]   = False
        g [True,True,False]   = False
        g [True,True,True]    = True

-- unable to handle tests such as this yet...
test3 :: IO ()
test3 = putStrLn $ runST $ do
  x0 <- newSTRef "x1"
  x1 <- newSTRef "x2"
  x2 <- newSTRef "x3"
  let op = synthesis 3 [x0,x1,x2] f
  showOP op
  where f [False,False,False] = [True,True,True]     -- 7
        f [False,False,True]  = [False,False,False]  -- 0
        f [False,True,False]  = [True,True,False]    -- 6
        f [False,True,True]   = [True,False,False]   -- 4
        f [True,False,False]  = [False,True,False]   -- 2
        f [True,False,True]   = [False,False,True]   -- 1
        f [True,True,False]   = [False,True,True]    -- 3
        f [True,True,True]    = [True,False,True]    -- 5

test4 :: Int -> IO ()
test4 n = putStrLn $ runST $ do
  xs <- mapM (newSTRef . (\i -> "[0..(n-1)]" ++ show i)) [0..(n-1)]
  y <- newSTRef "y"
  let op = synthesis (n+1) (xs ++ [y]) id
  showOP op

test4N :: Int -> IO ()
test4N n = putStrLn $ runST $ do
  xs <- mapM (newSTRef . (\i -> "[0..(n-1)]" ++ show i)) [0..(n-1)]
  y <- newSTRef "y"
  let op = synthesisNew n (xs ++ [y]) id
  showOP op

parity :: [Bool] -> Bool
parity xs = odd (length (filter id xs))

test5N :: IO ()
test5N = putStrLn $ runST $ do
  x0 <- newSTRef "x0"
  x1 <- newSTRef "x1"
  x2 <- newSTRef "x2"
  x3 <- newSTRef "x3"
  let op = synthesisNew 3 [x3,x2,x1,x0] f
  showOP op
  where f [False,False,False] = [True]   -- 1
        f [False, False, True] = [False] -- 0
        f [False, True, False] = [True] -- 1
        f [False, True, True] = [False] -- 0
        f [True, False, False] = [True] -- 1
        f [True, False, True] = [False] -- 0
        f [True, True, False] = [False] -- 0
        f [True, True, True] = [True] -- 1

test5 :: IO ()
test5 = putStrLn $ runST $ do
  x0 <- newSTRef "x0"
  x1 <- newSTRef "x1"
  x2 <- newSTRef "x2"
  x3 <- newSTRef "x3"
  let op = synthesis 4 [x3,x2,x1,x0] (uf f)
  showOP op
  where f [False,False,False] = True   -- 1
        f [False, False, True] = False -- 0
        f [False, True, False] = True -- 1
        f [False, True, True] = False -- 0
        f [True, False, False] = True -- 1
        f [True, False, True] = False -- 0
        f [True, True, False] = False -- 0
        f [True, True, True] = True -- 1

test6N :: IO ()
test6N = putStrLn $ runST $ do
  x0 <- newSTRef "x0"
  x1 <- newSTRef "x1"
  x2 <- newSTRef "x2"
  x3 <- newSTRef "x3"
  let op = synthesisNew 3 [x3,x2,x1,x0] f
  showOP op
  where f [False, False, False] = [False]
        f [False, False, True] = [True]
        f [False, True, False] = [False]
        f [False, True, True] = [True]
        f [True, False, False] = [False]
        f [True, False, True] = [True]
        f [True, True, False] = [True]
        f [True, True, True] = [False]

test6 :: IO ()
test6 = putStrLn $ runST $ do
  x0 <- newSTRef "x0"
  x1 <- newSTRef "x1"
  x2 <- newSTRef "x2"
  x3 <- newSTRef "x3"
  let op = synthesis 4 [x3,x2,x1,x0] (uf f)
  showOP op
  where f [False, False, False] = False
        f [False, False, True] = True
        f [False, True, False] = False
        f [False, True, True] = True
        f [True, False, False] = False
        f [True, False, True] = True
        f [True, True, False] = True
        f [True, True, True] = False
----------------------------------------------------------------------------------------
