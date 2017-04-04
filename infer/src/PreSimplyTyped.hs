module PreSimplyTyped(Type(..), Ptrm(..), ptrm_infer_type) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Product_Type;
import qualified Option;
import qualified Fun;
import qualified Arith;

data Type = TUnit | TVar Arith.Nat | TArr Type Type | TPair Type Type;

data Ptrm a = PUnit | PVar a | PApp (Ptrm a) (Ptrm a) | PFn a Type (Ptrm a)
  | PPair (Ptrm a) (Ptrm a) | PFst (Ptrm a) | PSnd (Ptrm a);

equal_type :: Type -> Type -> Bool;
equal_type (TArr x31 x32) (TPair x41 x42) = False;
equal_type (TPair x41 x42) (TArr x31 x32) = False;
equal_type (TVar x2) (TPair x41 x42) = False;
equal_type (TPair x41 x42) (TVar x2) = False;
equal_type (TVar x2) (TArr x31 x32) = False;
equal_type (TArr x31 x32) (TVar x2) = False;
equal_type TUnit (TPair x41 x42) = False;
equal_type (TPair x41 x42) TUnit = False;
equal_type TUnit (TArr x31 x32) = False;
equal_type (TArr x31 x32) TUnit = False;
equal_type TUnit (TVar x2) = False;
equal_type (TVar x2) TUnit = False;
equal_type (TPair x41 x42) (TPair y41 y42) =
  equal_type x41 y41 && equal_type x42 y42;
equal_type (TArr x31 x32) (TArr y31 y32) =
  equal_type x31 y31 && equal_type x32 y32;
equal_type (TVar x2) (TVar y2) = Arith.equal_nat x2 y2;
equal_type TUnit TUnit = True;

ptrm_infer_type ::
  forall a. (Eq a) => (a -> Maybe Type) -> Ptrm a -> Maybe Type;
ptrm_infer_type gamma PUnit = Just TUnit;
ptrm_infer_type gamma (PVar x) = gamma x;
ptrm_infer_type gamma (PApp a b) =
  (case (ptrm_infer_type gamma a, ptrm_infer_type gamma b) of {
    (Nothing, _) -> Nothing;
    (Just TUnit, _) -> Nothing;
    (Just (TVar _), _) -> Nothing;
    (Just (TArr _ _), Nothing) -> Nothing;
    (Just (TArr tau sigma), Just taua) ->
      (if equal_type tau taua then Just sigma else Nothing);
    (Just (TPair _ _), _) -> Nothing;
  });
ptrm_infer_type gamma (PFn x tau a) =
  (case ptrm_infer_type (Fun.fun_upd gamma x (Just tau)) a of {
    Nothing -> Nothing;
    Just sigma -> Just (TArr tau sigma);
  });
ptrm_infer_type gamma (PPair a b) =
  (case (ptrm_infer_type gamma a, ptrm_infer_type gamma b) of {
    (Nothing, _) -> Nothing;
    (Just _, Nothing) -> Nothing;
    (Just tau, Just sigma) -> Just (TPair tau sigma);
  });
ptrm_infer_type gamma (PFst p) = (case ptrm_infer_type gamma p of {
                                   Nothing -> Nothing;
                                   Just TUnit -> Nothing;
                                   Just (TVar _) -> Nothing;
                                   Just (TArr _ _) -> Nothing;
                                   Just (TPair tau _) -> Just tau;
                                 });
ptrm_infer_type gamma (PSnd p) = (case ptrm_infer_type gamma p of {
                                   Nothing -> Nothing;
                                   Just a -> (case a of {
       TUnit -> Nothing;
       TVar _ -> Nothing;
       TArr _ _ -> Nothing;
       TPair _ aa -> Just aa;
     });
                                 });

}
