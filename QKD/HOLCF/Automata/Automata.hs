{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Automata(Msg, Proc, Num, Transaction, Nat, Action, test_automaton)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import Data.Bits ((.&.), (.|.), (.^.));
import qualified Prelude;
import qualified Data.Bits;

data Msg a = Prepare a | Yes | No | Commit | Abort | Ack;

equal_msg :: forall a. (Eq a) => Msg a -> Msg a -> Bool;
equal_msg Abort Ack = False;
equal_msg Ack Abort = False;
equal_msg Commit Ack = False;
equal_msg Ack Commit = False;
equal_msg Commit Abort = False;
equal_msg Abort Commit = False;
equal_msg No Ack = False;
equal_msg Ack No = False;
equal_msg No Abort = False;
equal_msg Abort No = False;
equal_msg No Commit = False;
equal_msg Commit No = False;
equal_msg Yes Ack = False;
equal_msg Ack Yes = False;
equal_msg Yes Abort = False;
equal_msg Abort Yes = False;
equal_msg Yes Commit = False;
equal_msg Commit Yes = False;
equal_msg Yes No = False;
equal_msg No Yes = False;
equal_msg (Prepare x1) Ack = False;
equal_msg Ack (Prepare x1) = False;
equal_msg (Prepare x1) Abort = False;
equal_msg Abort (Prepare x1) = False;
equal_msg (Prepare x1) Commit = False;
equal_msg Commit (Prepare x1) = False;
equal_msg (Prepare x1) No = False;
equal_msg No (Prepare x1) = False;
equal_msg (Prepare x1) Yes = False;
equal_msg Yes (Prepare x1) = False;
equal_msg (Prepare x1) (Prepare y1) = x1 == y1;
equal_msg Ack Ack = True;
equal_msg Abort Abort = True;
equal_msg Commit Commit = True;
equal_msg No No = True;
equal_msg Yes Yes = True;

instance (Eq a) => Eq (Msg a) where {
  a == b = equal_msg a b;
};

data Proc = P0 | P1;

equal_proc :: Proc -> Proc -> Bool;
equal_proc P0 P1 = False;
equal_proc P1 P0 = False;
equal_proc P1 P1 = True;
equal_proc P0 P0 = True;

instance Eq Proc where {
  a == b = equal_proc a b;
};

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

data Transaction = T0;

equal_transaction :: Transaction -> Transaction -> Bool;
equal_transaction T0 T0 = True;

instance Eq Transaction where {
  a == b = equal_transaction a b;
};

data Nat = Zero_nat | Suc Nat;

data Action a b = Start a | Send a a b | Receive a a b | Timeout a | Restart a;

member :: forall a. (Eq a) => [a] -> a -> Bool;
member [] y = False;
member (x : xs) y = x == y || member xs y;

length_tailrec :: forall a. [a] -> Nat -> Nat;
length_tailrec [] n = n;
length_tailrec (x : xs) n = length_tailrec xs (Suc n);

exec_step ::
  [(Proc, (Proc, Msg Transaction))] ->
    Action Proc (Msg Transaction) -> Maybe [(Proc, (Proc, Msg Transaction))];
exec_step ma (Send s r m) =
  Just (if member ma (s, (r, m)) then ma else (s, (r, m)) : ma);
exec_step ma (Receive s r m) =
  (if member ma (s, (r, m)) then Just ma else Nothing);
exec_step m (Start v) = Nothing;
exec_step m (Timeout v) = Nothing;
exec_step m (Restart v) = Nothing;

exec_run ::
  [Action Proc (Msg Transaction)] ->
    [(Proc, (Proc, Msg Transaction))] ->
      Maybe [(Proc, (Proc, Msg Transaction))];
exec_run [] m = Just m;
exec_run (a : asa) m = (case exec_step m a of {
                         Nothing -> Nothing;
                         Just aa -> exec_run asa aa;
                       });

size_list :: forall a. [a] -> Nat;
size_list xs = length_tailrec xs Zero_nat;

of_nat_aux :: forall a. (Semiring_1 a) => (a -> a) -> Nat -> a -> a;
of_nat_aux inc Zero_nat i = i;
of_nat_aux inc (Suc n) i = of_nat_aux inc n (inc i);

of_nat :: forall a. (Semiring_1 a) => Nat -> a;
of_nat n = of_nat_aux (\ i -> plus i one) n zero;

integer_of_nat :: Nat -> Integer;
integer_of_nat = of_nat;

test_automaton :: Integer -> Integer;
test_automaton n =
  (case exec_run
          [Send P0 P1 (Prepare T0), Receive P0 P1 (Prepare T0), Send P1 P0 Ack,
            Receive P1 P0 Ack]
          []
    of {
    Nothing -> (-1 :: Integer);
    Just m -> integer_of_nat (size_list m);
  });

}
