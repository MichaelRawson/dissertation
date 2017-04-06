module Main where

import Data.List (break)
import qualified Data.Map as Map

-- benchmarking framework
import Criterion.Main

-- extracted modules
import Arith
import PreSimplyTyped
import SimplyTyped

-- utilities
import Utils

-- alternative implementations
inferMap :: Map.Map Nat Type -> Trm Nat -> Maybe Type
inferMap ctx (Abs_trm t) = inferMap' ctx t
  where
  inferMap' ctx t = case t of
    PUnit -> pure TUnit
    PVar x -> Map.lookup x ctx
    PFn x t m -> TArr t <$> inferMap' (Map.insert x t ctx) m
    PApp l r -> do
      t1 <- inferMap' ctx l
      t2 <- inferMap' ctx r
      case t1 of
        TArr a b -> if t2 == a
          then pure b
          else Nothing
        _ -> Nothing
    PPair l r -> do
      t1 <- inferMap' ctx l
      t2 <- inferMap' ctx r
      pure $ TPair t1 t2
    PFst p -> do
      t <- inferMap' ctx p
      case t of
        TPair t1 _ -> pure t1
        _ -> Nothing
    PSnd p -> do
      t <- inferMap' ctx p
      case t of
        TPair _ t2 -> pure t2
        _ -> Nothing

-- run the benchmark
main :: IO ()
main = do
  input <- readFile "samples.dat"
  let benchmarks = map readBench . lines $ input
  defaultMain [bgroup "infer" benchmarks]

  where
  underTest = inferMap emptyContext --infer (convertContext emptyContext)
  readBench line = case break (== '\t') line of
    (l, r) -> let
      term = read l :: Trm Nat
      size = read r :: Int
      in bench (show size) $ nf underTest term
