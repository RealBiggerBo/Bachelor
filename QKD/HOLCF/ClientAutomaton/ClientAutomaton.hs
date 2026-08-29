{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  ClientAutomaton(Exec_msg(..), Exec_action(..), Client_exec_state(..),
                   initial_client, client_exec_step)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import Data.Bits ((.&.), (.|.), (.^.));
import qualified Prelude;
import qualified Data.Bits;

class Ord a where {
  less_eq :: a -> a -> Bool;
  less :: a -> a -> Bool;
};

instance Ord Integer where {
  less_eq = (\ a b -> a <= b);
  less = (\ a b -> a < b);
};

data Exec_msg = CounterMsg Integer | Ping | Pong;

data Exec_action = Receive Integer Exec_msg | UpdateCounter | PingServer
  | ClientJoined Integer;

data Client_exec_state = ClientState Integer Integer;

max :: forall a. (Ord a) => a -> a -> a;
max a b = (if less_eq a b then b else a);

initial_client :: Integer -> Client_exec_state;
initial_client server = ClientState (0 :: Integer) server;

client_exec_step ::
  Client_exec_state ->
    Exec_action -> (Client_exec_state, [(Integer, Exec_msg)]);
client_exec_step (ClientState ca s) (Receive uu (CounterMsg c)) =
  (ClientState (max ca c) s, []);
client_exec_step (ClientState c s) PingServer = (ClientState c s, [(s, Ping)]);
client_exec_step s (Receive v Ping) = (s, []);
client_exec_step s (Receive v Pong) = (s, []);
client_exec_step s UpdateCounter = (s, []);
client_exec_step s (ClientJoined v) = (s, []);

}
