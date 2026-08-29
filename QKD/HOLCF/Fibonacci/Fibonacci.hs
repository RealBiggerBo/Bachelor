{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Fibonacci(Nat, fib_int) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import Data.Bits ((.&.), (.|.), (.^.));
import qualified Prelude;
import qualified Data.Bits;

data Num = One | Bit0 Num | Bit1 Num;

one_integer :: Integer;
one_integer = (1 :: Integer);

class One a where {
  one :: a;
};

instance One Integer where {
  one = one_integer;
};

class Plus a where {
  plus :: a -> a -> a;
};

instance Plus Integer where {
  plus = (\ a b -> a + b);
};

class Zero a where {
  zero :: a;
};

instance Zero Integer where {
  zero = (0 :: Integer);
};

class (Plus a) => Semigroup_add a where {
};

class (One a, Semigroup_add a) => Numeral a where {
};

instance Semigroup_add Integer where {
};

instance Numeral Integer where {
};

class Times a where {
  times :: a -> a -> a;
};

class (One a, Times a) => Power a where {
};

instance Times Integer where {
  times = (\ a b -> a * b);
};

instance Power Integer where {
};

class (Semigroup_add a) => Ab_semigroup_add a where {
};

class (Times a) => Semigroup_mult a where {
};

class (Ab_semigroup_add a, Semigroup_mult a) => Semiring a where {
};

instance Ab_semigroup_add Integer where {
};

instance Semigroup_mult Integer where {
};

instance Semiring Integer where {
};

class (Times a, Zero a) => Mult_zero a where {
};

instance Mult_zero Integer where {
};

class (Semigroup_add a, Zero a) => Monoid_add a where {
};

class (Ab_semigroup_add a, Monoid_add a) => Comm_monoid_add a where {
};

class (Comm_monoid_add a, Mult_zero a, Semiring a) => Semiring_0 a where {
};

instance Monoid_add Integer where {
};

instance Comm_monoid_add Integer where {
};

instance Semiring_0 Integer where {
};

class (Semigroup_mult a, Power a) => Monoid_mult a where {
};

class (Monoid_mult a, Numeral a, Semiring a) => Semiring_numeral a where {
};

class (One a, Zero a) => Zero_neq_one a where {
};

class (Semiring_numeral a, Semiring_0 a, Zero_neq_one a) => Semiring_1 a where {
};

instance Monoid_mult Integer where {
};

instance Semiring_numeral Integer where {
};

instance Zero_neq_one Integer where {
};

instance Semiring_1 Integer where {
};

data Nat = Zero_nat | Suc Nat;

plus_nat :: Nat -> Nat -> Nat;
plus_nat Zero_nat n = n;
plus_nat (Suc m) n = plus_nat m (Suc n);

one_nat :: Nat;
one_nat = Suc Zero_nat;

fib :: Nat -> Nat;
fib Zero_nat = Zero_nat;
fib (Suc Zero_nat) = one_nat;
fib (Suc (Suc n)) = plus_nat (fib n) (fib (Suc n));

apsnd :: forall a b c. (a -> b) -> (c, a) -> (c, b);
apsnd f (x, y) = (x, f y);

divmod_integer :: Integer -> Integer -> (Integer, Integer);
divmod_integer k l =
  (if k == (0 :: Integer) then ((0 :: Integer), (0 :: Integer))
    else (if (0 :: Integer) < l
           then (if (0 :: Integer) < k then divMod (abs k) (abs l)
                  else (case divMod (abs k) (abs l) of {
                         (r, s) ->
                           (if s == (0 :: Integer)
                             then (negate r, (0 :: Integer))
                             else (negate r - (1 :: Integer), l - s));
                       }))
           else (if l == (0 :: Integer) then ((0 :: Integer), k)
                  else apsnd negate
                         (if k < (0 :: Integer) then divMod (abs k) (abs l)
                           else (case divMod (abs k) (abs l) of {
                                  (r, s) ->
                                    (if s == (0 :: Integer)
                                      then (negate r, (0 :: Integer))
                                      else (negate r - (1 :: Integer),
     negate l - s));
                                })))));

nat_of_integer :: Integer -> Nat;
nat_of_integer k =
  (if k <= (0 :: Integer) then Zero_nat
    else (case divmod_integer k (2 :: Integer) of {
           (l, j) ->
             let {
               la = nat_of_integer l;
               lb = plus_nat la la;
             } in (if j == (0 :: Integer) then lb else plus_nat lb one_nat);
         }));

of_nat_aux :: forall a. (Semiring_1 a) => (a -> a) -> Nat -> a -> a;
of_nat_aux inc Zero_nat i = i;
of_nat_aux inc (Suc n) i = of_nat_aux inc n (inc i);

of_nat :: forall a. (Semiring_1 a) => Nat -> a;
of_nat n = of_nat_aux (\ i -> plus i one) n zero;

integer_of_nat :: Nat -> Integer;
integer_of_nat = of_nat;

fib_int :: Integer -> Integer;
fib_int n = integer_of_nat (fib (nat_of_integer n));

}
