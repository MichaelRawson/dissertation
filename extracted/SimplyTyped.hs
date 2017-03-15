module SimplyTyped(Trm(..), infer) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Fresh;
import qualified PreSimplyTyped;

newtype Trm a = Abs_trm (PreSimplyTyped.Ptrm a) deriving (Prelude.Show);

infer ::
  forall a.
    (Fresh.Fresh a,
      Eq a) => (a -> Maybe PreSimplyTyped.Type) ->
                 Trm a -> Maybe PreSimplyTyped.Type;
infer xb (Abs_trm xa) = PreSimplyTyped.ptrm_infer_type xb xa;

}
