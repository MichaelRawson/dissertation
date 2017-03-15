import Test.Hspec
import Test.QuickCheck

import Arith
import Fresh
import Set
import SimplyTyped
import PreSimplyTyped

int_nat :: Int -> Nat
int_nat 0 = Zero_nat
int_nat n = Suc (int_nat (n - 1))

instance Arbitrary Nat where
  arbitrary = do
    n <- choose (1, 100)
    pure . int_nat $ n

main :: IO ()
main = hspec $ do
  let z = Zero_nat
  let sensible = choose (1, 100)
  let infer' c p = infer c (Abs_trm p)
  let empty = const Nothing
  let single n = if n == z then Just (TVar z) else Nothing

  describe "fresh variables" $ do
    it "fresh in a set" $ do
      property $ forAll (listOf sensible) $ \l -> let l' = map int_nat l in fresh_in (Set l') `notElem` l'
  describe "inference of variables" $ do
    it "undefined in the empty context" $ do
      property $ \n -> (infer' empty $ PVar (n :: Nat)) == Nothing

    it "undefined if fresh in a context" $ do
      let fresh_ctx n x = if n == x then Nothing else Just (TVar z) 
      property $ \n -> (infer' (fresh_ctx n) $ PVar (n :: Nat)) == Nothing

    it "defined if in a context" $ do
      let hit = Just (TVar z)
      let ctx n x = if n == x then hit else Nothing
      property $ \n -> (infer' (ctx n) $ PVar (n :: Nat)) == hit

  describe "inference of lambdas" $ do
    it "propagates type errors" $ do
      property $ \n -> (infer' empty $ PFn (n :: Nat) (TVar z) (PVar z)) == Nothing
    it "binds variables" $ do
      property $ \n -> (infer' empty $ PFn (n :: Nat) (TVar z) (PVar n)) == Just (TArr (TVar z) (TVar z))

    it "doesn't bind extraneous variables" $ do
      let ctx n x = if n == x then Just (TVar (int_nat 1)) else Nothing
      property $ \n -> (infer' (ctx n) $ PFn z (TVar z) (PVar (n :: Nat))) == Just (TArr (TVar z) (TVar (int_nat 1)))

  describe "inference of applications" $ do
    it "propagates type errors on the left" $ do
      infer' single (PApp (PVar (int_nat 1)) (PVar z)) `shouldBe` Nothing
    it "propagates type errors on the right" $ do
      infer' single (PApp (PVar z) (PVar (int_nat 1))) `shouldBe` Nothing
    it "undefined for non-function application" $ do
      infer' single (PApp (PVar z) (PVar z)) `shouldBe` Nothing
    it "undefined for type mismatch" $ do
      infer' single (PApp (PFn z (TVar (int_nat 1)) (PVar z)) (PVar z)) `shouldBe` Nothing
    it "infers correct type" $ do
      let ctx n x = if n == x then Just (TVar x) else if z == x then Just (TVar z) else Nothing
      property $ \n -> infer' (ctx n) (PApp (PFn (n :: Nat) (TVar n) (PVar z)) (PVar n)) == Just (TVar z)
