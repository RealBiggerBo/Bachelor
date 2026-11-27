theory Automata_Export_Test_Exec
  imports
    Automata_Export_Test
    "HOL-Library.Code_Target_Int"
begin

type_synonym process = integer

datatype exec_msg = CounterMsg (CounterMsg_curCounter: integer) | Ping | Pong

datatype exec_action = 
  Receive (Receive_sender: process) (Receive_msg: exec_msg) | 
  UpdateCounter | 
  PingServer |
  ClientJoined (ClientJoined_newClient: process)

(* ================================================================ *)
(* Server implementation                                            *)
(* ================================================================ *)

datatype server_exec_state = ServerState (server_exec_state_curCounter: integer) (server_exec_state_clients: "process list")

fun generateMsgs:: "process list \<Rightarrow> exec_msg \<Rightarrow> (process \<times> exec_msg) list" where
"generateMsgs [] _ = []" |
"generateMsgs (p#ps) msg = (p, msg)#(generateMsgs ps msg)"

fun server_exec_step:: "server_exec_state \<Rightarrow> exec_action \<Rightarrow> server_exec_state \<times> (process \<times> exec_msg) list" where
"server_exec_step (ServerState c clients) UpdateCounter = (ServerState (c + 1) clients, generateMsgs clients (CounterMsg (c + 1)))" |
"server_exec_step s (Receive client Ping) = (s, [(client, Pong)])" |
"server_exec_step (ServerState c clients) (ClientJoined p) = (ServerState c (p#clients), [])" |
"server_exec_step s _ = (s, [])"

definition initial_server:: "server_exec_state" where
"initial_server = ServerState 0 []"


export_code
  server_exec_step
  initial_server
  ServerState
  CounterMsg Ping Pong
  Receive UpdateCounter PingServer ClientJoined
in Haskell
  module_name ServerAutomaton
  file "ServerAutomaton"


(* ================================================================ *)
(* Client implementation                                            *)
(* ================================================================ *)

datatype client_exec_state = ClientState (ClientState_curCounter: integer) (ClientState_serverId: process)

fun client_exec_step:: "client_exec_state \<Rightarrow> exec_action \<Rightarrow> client_exec_state \<times> (process \<times> exec_msg) list" where
"client_exec_step (ClientState c s) (Receive _ (CounterMsg c')) = (ClientState (max c c') s, [])" |
"client_exec_step (ClientState c s) PingServer = (ClientState c s, [(s,Ping)])" |
"client_exec_step s _ = (s, [])"

definition initial_client:: "process \<Rightarrow> client_exec_state" where
"initial_client server = ClientState 0 server"


export_code
  client_exec_step
  initial_client
  ClientState
  CounterMsg Ping Pong
  Receive UpdateCounter PingServer ClientJoined
in Haskell
  module_name ClientAutomaton
  file "ClientAutomaton"

end