module Fresh(Fresh(..), fresh_in_nat) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Lattices_Big;
import qualified Arith;
import qualified Set;

class Fresh a where {
  fresh_in :: Set.Set a -> a;
};

fresh_in_nat :: Set.Set Arith.Nat -> Arith.Nat;
fresh_in_nat s =
  (if Set.is_empty s then Arith.Zero_nat
    else Arith.plus_nat (Lattices_Big.max s) Arith.one_nat);

}
