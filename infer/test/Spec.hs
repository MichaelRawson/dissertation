module Main where

import Data.Maybe (isJust, fromJust)

-- testing frameworks
import Test.Hspec
import Test.QuickCheck

-- extracted code modules
import Arith
import Fresh
import Set
import SimplyTyped
import PreSimplyTyped

-- code for producing random terms
import Utils

main :: IO ()
main = hspec $ do
  let failure = Nothing

  describe "fresh variables" $ do
    it "fresh in a set" $ do
      property $
        forAll (listOf nats) $ \l ->
        fresh_in (Set l) `notElem` l

  describe "unit inference" $ do
    it "infers unit values to have unit type" $ do
      property $
        forAll contexts $ \c ->
        infer' c PUnit `shouldBe` pure TUnit

  describe "inference of variables" $ do
    it "undefined in the empty context" $
      property $
        forAll nats $ \n -> 
        infer' emptyContext (PVar n) `shouldBe` failure

    it "undefined if fresh in a context" $ do
      property $
        forAll contexts $ \c ->
        forAll nats $ \n ->
        infer' (n `removedFromContext` c) (PVar n) `shouldBe` failure

    it "infers the correct type if in a context" $ do
      property $
        forAll contexts $ \c ->
        forAll nats $ \n ->
        forAll (sized types) $ \t ->
        let c' = (n, t) `addedToContext` c in
          infer' c' (PVar n) `shouldBe` pure t

  describe "inference of lambdas" $ do
    it "propagates type errors" $ do
      property $
        forAll contexts $ \c ->
        forAll nats $ \n ->
        forAll (sized types) $ \t ->
        forAll (sized . illTypedTerms $ (n, t) `addedToContext` c) $ \m ->
        infer' c (PFn n t m) `shouldBe` failure

    it "doesn't bind extraneous variables" $ do
      property $
        forAll contexts $ \c ->
        forAll nats $ \n -> forAll nats $ \m -> (n /= m) ==>
        forAll (sized types) $ \t ->
        let c' = (n, t) `addedToContext` c in
          infer' c (PFn n t (PVar m)) `shouldBe` TArr t <$> infer' c' (PVar m)

    it "infers a correct type" $ do
      property $
        forAll contexts $ \c ->
        forAll nats $ \n ->
        forAll (sized types) $ \t ->
        let c' = (n, t) `addedToContext` c in
        forAll (sized . wellTypedTerms $ c') $ \m ->
          infer' c (PFn n t m) `shouldBe` TArr t <$> infer' c' m

  describe "inference of applications" $ do
    it "propagates type errors on the left" $ do
      property $
        forAll contexts $ \c ->
        forAll (sized $ illTypedTerms c) $ \l ->
        forAll (sized $ wellTypedTerms c) $ \r ->
        infer' c (PApp l r) `shouldBe` failure

    it "propagates type errors on the right" $ do
      property $
        forAll contexts $ \c ->
        forAll (sized $ wellTypedTerms c) $ \l ->
        forAll (sized $ illTypedTerms c) $ \r ->
        infer' c (PApp l r) `shouldBe` failure

    it "undefined for non-arrow application" $ do
      property $
        forAll contexts $ \c ->
        forAll (sized $ notArrowTypes c) $ \l ->
        forAll (sized $ wellTypedTerms c) $ \r ->
        infer' c (PApp l r) `shouldBe` failure

    it "undefined for type mismatch" $ do
      property $
        forAll contexts $ \c ->
        forAll nats $ \n ->
        forAll (sized $ wellTypedTerms c) $ \l ->
        forAll (sized $ wellTypedTerms c) $ \r ->
        forAll (sized types) $ \t -> (infer' c r /= pure t) ==>
        infer' c (PApp (PFn n t l) r) `shouldBe` failure

    it "infers correct type" $ do
      property $
        forAll contexts $ \c ->
        forAll nats $ \n ->
        forAll (sized $ wellTypedTerms c) $ \r ->
        let
          t2 = fromJust . infer' c $ r
          c' = (n, t2) `addedToContext` c in 
        forAll (sized $ wellTypedTerms c') $ \l ->
        infer' c (PApp (PFn n t2 l) r) `shouldBe` (infer' c' l)

  describe "inference of pairs" $ do
    it "propagates type errors on the left" $ do
      property $
        forAll contexts $ \c ->
        forAll (sized $ illTypedTerms c) $ \l ->
        forAll (sized $ wellTypedTerms c) $ \r ->
        infer' c (PPair l r) `shouldBe` failure

    it "propagates type errors on the right" $ do
      property $
        forAll contexts $ \c ->
        forAll (sized $ wellTypedTerms c) $ \l ->
        forAll (sized $ illTypedTerms c) $ \r ->
        infer' c (PPair l r) `shouldBe` failure

    it "infers correct type" $ do
      property $
        forAll contexts $ \c ->
        forAll (sized $ wellTypedTerms c) $ \l ->
        forAll (sized $ wellTypedTerms c) $ \r ->
        infer' c (PPair l r) `shouldBe` TPair <$> infer' c l <*> infer' c r

  describe "testing assumptions" $ do
    it "ill-typed terms are ill-typed" $ do
      property $
        forAll contexts $ \c ->
        forAll (sized $ illTypedTerms c) $ \m ->
        infer' c m `shouldBe` failure

    it "well-typed terms are well-typed" $ do
      property $
        forAll contexts $ \c ->
        forAll (sized $ wellTypedTerms c) $ \m ->
        isJust $ infer' c m
