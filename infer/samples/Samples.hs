module Main where

import Control.Monad (forM_)
import Test.QuickCheck

import Utils
import SimplyTyped

main :: IO ()
main = do
  let sizes = [1 .. 100]
  let generators = [resize n (sized $ wellTypedTerms emptyContext) | n <- sizes]
  forM_ (zip sizes generators) $ \(n, g) -> do
    s <- generate g
    putStrLn $ show (Abs_trm s) ++ "\t" ++ show n
