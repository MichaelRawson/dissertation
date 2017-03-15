module Main where

-- extracted modules
import Arith
import PreSimplyTyped
import SimplyTyped

-- benchmarking framework
import Criterion.Main

-- generate a term of arbitrary size
generateTrm :: Int -> Trm Nat
generateTrm = Abs_trm . generateTrm' Zero_nat
  where
  generateTrm' vars size
    | (size == 0) = PUnit
    | (size == 1) = PVar $ case vars of
      Suc n -> n
      Zero_nat -> Zero_nat
    | (size `mod` 3 == 0) = let
      t1 = generateTrm' (Suc vars) (size `div` 2 - 1)
      t2 = generateTrm' vars (size `div` 2)
      in PApp (PFn vars (TUnit) t1) t2 
    | (size `mod` 3 == 1) = let
      t1 = generateTrm' vars (size `div` 2 -1)
      t2 = generateTrm' vars (size `div` 2)
      in PFst (PPair t1 t2)
    | (size `mod` 3 == 2) = let
      t1 = generateTrm' vars (size `div` 2 - 1)
      t2 = generateTrm' vars (size `div` 2)
      in PSnd (PPair t1 t2)

-- infer the type of a term of arbitrary size
infer' :: Int -> Maybe Type
infer' = infer ctx . generateTrm where
  ctx n = if n == Zero_nat then Just TUnit else Nothing

-- run the benchmark
main = defaultMain [
  bgroup "infer"
    [
    bench "0.1"  $ whnf infer' 100000,
    bench "0.2"  $ whnf infer' 200000,
    bench "0.3"  $ whnf infer' 300000,
    bench "0.4"  $ whnf infer' 400000,
    bench "0.5"  $ whnf infer' 500000,
    bench "0.6"  $ whnf infer' 600000,
    bench "0.7"  $ whnf infer' 700000,
    bench "0.8"  $ whnf infer' 800000,
    bench "0.9"  $ whnf infer' 900000,
    bench "1.0"  $ whnf infer' 1000000,
    bench "1.1"  $ whnf infer' 1100000,
    bench "1.2"  $ whnf infer' 1200000,
    bench "1.3"  $ whnf infer' 1300000,
    bench "1.4"  $ whnf infer' 1400000,
    bench "1.5"  $ whnf infer' 1500000,
    bench "1.6"  $ whnf infer' 1600000,
    bench "1.7"  $ whnf infer' 1700000,
    bench "1.8"  $ whnf infer' 1800000,
    bench "1.9"  $ whnf infer' 1900000,
    bench "2.0"  $ whnf infer' 20000000
    ]
  ]
