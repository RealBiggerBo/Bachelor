{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  ServerAutomaton(Num, Exec_msg(..), Exec_action(..), Server_exec_state(..),
                   initial_server, server_exec_step)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import Data.Bits ((.&.), (.|.), (.^.));
import qualified Prelude;
import qualified Data.Bits;

data Num = One | Bit0 Num | Bit1 Num;

data Exec_msg = CounterMsg Integer | Ping | Pong;

data Exec_action = Receive Integer Exec_msg | UpdateCounter | PingServer
  | ClientJoined Integer;

data Server_exec_state = ServerState Integer [Integer];

generateMsgs :: [Integer] -> Exec_msg -> [(Integer, Exec_msg)];
generateMsgs [] uu = [];
generateMsgs (p : ps) msg = (p, msg) : generateMsgs ps msg;

initial_server :: Server_exec_state;
initial_server = ServerState (0 :: Integer) [];

server_exec_step ::
  Server_exec_state ->
    Exec_action -> (Server_exec_state, [(Integer, Exec_msg)]);
server_exec_step (ServerState c clients) UpdateCounter =
  (ServerState (c + (1 :: Integer)) clients,
    generateMsgs clients (CounterMsg (c + (1 :: Integer))));
server_exec_step s (Receive client Ping) = (s, [(client, Pong)]);
server_exec_step (ServerState c clients) (ClientJoined p) =
  (ServerState c (p : clients), []);
server_exec_step s (Receive v (CounterMsg vb)) = (s, []);
server_exec_step s (Receive v Pong) = (s, []);
server_exec_step s PingServer = (s, []);

}
