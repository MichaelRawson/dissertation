module Main where

import Control.Monad (forM_)
import qualified Data.Map as Map

import Utils
import Arith
import Fresh
import Set
import PreSimplyTyped
import SimplyTyped

benchFn :: Int -> Term
benchFn n
  | (n <= 0) = PUnit
  | otherwise = PFn Zero_nat TUnit . benchFn $ n - 1

benchLookup :: Int -> Term
benchLookup n = benchLookup' n
  where
  benchLookup' m
    | (m <= 0) = PVar (Suc Zero_nat)
    | (m < partition) = let
      m' = m - 1
      m1 = m `div` 2
      m2 = m' - m1
      in PPair (benchLookup' m1) (benchLookup' m2)
    | otherwise = PFn Zero_nat TUnit . benchLookup' $ m - 1
  partition = n `div` 2

benchApp :: Int -> Term
benchApp n
  | (n <= 0) = PUnit
  | otherwise = PApp
    (PFn Zero_nat TUnit $ benchApp n1)
    (benchApp n2)
  where
  n' = n - 2
  n1 = n' `div` 2
  n2 = n' - n1

benchBiasedApp :: Int -> Term
benchBiasedApp n
  | (n <= 0) = PUnit
  | otherwise = PApp
    (PFn Zero_nat TUnit PUnit)
    (benchBiasedApp n')
  where
  n' = n - 2

benchPair :: Int -> Term
benchPair n
  | (n <= 0) = PUnit
  | otherwise = PPair
    (benchPair n1)
    (benchPair n2)
  where
  n' = n - 1
  n1 = n' `div` 2
  n2 = n' - n1

benchProjections :: Int -> Term
benchProjections n
  | (n <= 0) = PUnit
  | ((n `div` 2) `mod` 2 == 0) = PSnd . PPair PUnit $ benchProjections (n - 2)
  | otherwise = PFst . flip PPair PUnit $ benchProjections (n - 2)

benchWellTyped :: Int -> Term
benchWellTyped = benchWellTyped' emptyContext
  where
  benchWellTyped' ctx n
    | (n == 1 && not (Map.null ctx)) = PVar . fst . Map.findMax $ ctx
    | (n <= 1) = PUnit
    | (n `mod` 5 == 0) = let
      x = fresh_in . Set . Map.keys $ ctx
      in PFn x TUnit . benchWellTyped' ((x, TUnit) `addedToContext` ctx) $ n - 1
    | (n `mod` 5 == 1) = let
      n' = n - 1
      n1 = n `div` 2
      n2 = n' - n1
      in PPair (benchWellTyped' ctx n1) (benchWellTyped' ctx n2)
    | (n `mod` 5 == 2 || n `mod` 5 == 3) = let
      op = if n `mod` 3 == 0 then PFst else PSnd
      n' = n - 1
      n1 = n' `div` 2
      n2 = n' - n1
      in op $ PPair (benchWellTyped' ctx n1) (benchWellTyped' ctx n2)
    | (n `mod` 5 == 4) = let
      n' = n - 2
      n1 = n' `div` 2
      n2 = n' - n1
      m2 = benchWellTyped' ctx n1
      Just t2 = infer' ctx $ m2
      x = fresh_in . Set . Map.keys $ ctx
      in PApp
        (PFn x t2 $ benchWellTyped' ((x, t2) `addedToContext` ctx) n1)
        m2

main :: IO ()
main = do
  let
    sizes = [1, 10, 100, 1000, 10000, 100000]
    bench = benchWellTyped

  forM_ sizes $ \n -> do
    let sample = Abs_trm . bench $ n
    putStrLn $ show sample ++ "\t" ++ show n
