module Utils where

import GHC.Generics (Generic)
import Control.DeepSeq (NFData)

import Data.Maybe (isNothing, fromJust)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Test.QuickCheck

import Arith
import Set
import Fresh
import PreSimplyTyped
import SimplyTyped


-- instances not provided with the extracted code
deriving instance Eq Nat
deriving instance Ord Nat
deriving instance Show Nat
deriving instance Read Nat
deriving instance Generic Nat
deriving instance NFData Nat

instance Fresh Nat where
  fresh_in = fresh_in_nat

deriving instance Eq Type
deriving instance Show Type
deriving instance Read Type
deriving instance Generic Type
deriving instance NFData Type

deriving instance Show Term
deriving instance Read Term
deriving instance Generic Term
deriving instance NFData Term

deriving instance Show (Trm Nat)
deriving instance Read (Trm Nat)
deriving instance Generic (Trm Nat)
deriving instance NFData (Trm Nat)

-- conveniences
type Term = Ptrm Nat
type Context = Map.Map Nat Type

convertContext :: Map.Map Nat Type -> (Nat -> Maybe Type)
convertContext = flip Map.lookup

infer' :: Context -> Term -> Maybe Type
infer' m p = infer (convertContext m) (Abs_trm p)

-- generators for arbitrary things
nats :: Gen Nat
nats = let
  int_nat :: Int -> Nat
  int_nat 0 = Zero_nat
  int_nat n = Suc (int_nat (n - 1))
  in int_nat <$> choose (0, 10)

instance Arbitrary Nat where
  arbitrary = nats

contexts :: Gen Context
contexts = arbitrary

types :: Int -> Gen Type
types n
  | (n <= 0) = do
    choice <- choose (1, 2) :: Gen Int
    case choice of
      1 -> pure TUnit
      2 -> TVar <$> arbitrary
  | otherwise = do
    choice <- choose (1, 2) :: Gen Int
    partition <- choose (0, n) :: Gen Int
    t1 <- types $ partition - 1
    t2 <- types $ n - partition - 1
    case choice of
      1 -> pure $ TArr t1 t2
      2 -> pure $ TPair t1 t2

instance Arbitrary Type where
  arbitrary = sized types

terms :: Int -> Gen Term
terms n
  | (n <= 1) = do
    var <- arbitrary
    if var
      then PVar <$> arbitrary
      else pure PUnit
  | otherwise = do
    choice <- choose (1, 5) :: Gen Int
    partition <- choose (1, n - 1) :: Gen Int
    case choice of
      1 -> PFn <$> arbitrary <*> arbitrary <*> terms (n - 1)
      2 -> PApp  <$> terms partition <*> terms (n - partition)
      3 -> PPair <$> terms partition <*> terms (n - partition)
      4 -> PFst <$> terms (n - 1)
      5 -> PSnd <$> terms (n - 1)

instance Arbitrary Term where 
  arbitrary = sized terms

illTypedTerms :: Context -> Int -> Gen Term
illTypedTerms ctx n = terms n `suchThat` (isNothing . infer' ctx)

wellTypedTerms :: Context -> Int -> Gen Term
wellTypedTerms map n
  | (n <= 1 && Map.null map) = pure PUnit
  | (n <= 1) = do
  var <- arbitrary
  if var
    then do
      x <- elements . Map.keys $ map
      pure . PVar $ x
    else pure PUnit
  | otherwise = do
  unary <- arbitrary
  if unary
    then do
      term <- wellTypedTerms map  (n - 1)
      let t = fromJust . infer' map $ term

      case t of
        TPair _ _ -> do
          choice <- elements [PFst, PSnd]
          pure . choice $ term
        _ -> do
          t <- arbitrary
          let
            x = fresh_in . Set . Map.keys $ map
            map' = Map.insert x t map
          term <- wellTypedTerms map' (n - 1)
          pure $ PFn x t term
  else do
    partition <- choose (1, n - 1)
    let
      s1 = partition
      s2 = n - partition
    pair <- arbitrary
    if pair
      then do
        t1 <- wellTypedTerms map s1
        t2 <- wellTypedTerms map s2
        pure $ PPair t1 t2
      else do
        t2 <- wellTypedTerms map s2
        let
          t = fromJust . infer' map $ t2
          x = fresh_in . Set . Map.keys $ map
          map' = Map.insert x t map
        t1 <- wellTypedTerms map' (s1 - 1)
        pure $ PApp (PFn x t t1) t2

notArrowTypes :: Context -> Int -> Gen Term
notArrowTypes ctx n = (wellTypedTerms ctx n) `suchThat` (not . isFn)
  where
  isFn m = case infer' ctx m of
    Just (TArr _ _) -> True
    _ -> False

-- typing environments
emptyContext :: Context
emptyContext = Map.empty

addedToContext :: (Nat, Type) -> Context -> Context
addedToContext (n, t) ctx = Map.insert n t ctx

removedFromContext :: Nat -> Context -> Context
removedFromContext = Map.delete
