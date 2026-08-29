theory Automata_Export_Test
  imports Automata_Helper
begin

(* --- Datatypes --- *)
datatype msg = CounterMsg nat | Ping | Pong

datatype ('proc, 'msg) action = 
  UpdateCount (UpdateCount_target: 'proc) | 
  PingServer (PingServer_target: 'proc) |
  ClientJoined (ClientJoined_target: 'proc) (ClientJoined_client: 'proc) |
  Send (Send_sender: 'proc) (Send_rcpt: 'proc) (Send_msg: 'msg) | 
  Receive (Receive_sender: 'proc) (Receive_rcpt: 'proc) (Receive_msg: 'msg)


(* --- Server --- *)
datatype 'proc sstate = Count (Count_clientIDs: "'proc set") (Count_curCounter: nat)
datatype 'proc server_state = Buffer (server_state_curState: "'proc sstate") (server_state_msgBuffer: "('proc \<times> 'proc \<times> msg) set")

fun server_step:: "'proc sstate \<Rightarrow> ('proc, msg) action \<Rightarrow> 'proc sstate \<times> ('proc \<times> msg) set" where
  \<open>server_step (Count clients counter) (UpdateCount _) = (Count clients (counter + 1), {(client, CounterMsg (counter + 1)) | client. client \<in> clients})\<close> |
  \<open>server_step (Count clients counter) (ClientJoined _ newClient) = (Count (clients \<union> {newClient}) counter, {})\<close> |
  \<open>server_step state (Receive client _ Ping) = (state, {(client, Pong)})\<close> |
  \<open>server_step state _ = (state, {})\<close>

definition server_trans:: "'proc \<Rightarrow> ('proc server_state \<times> ('proc, msg) action \<times> 'proc server_state) set" where
"server_trans pid =
  {(Buffer s msgs, UpdateCount pid, Buffer s' (msgs \<union> ((\<lambda>msg. (pid, msg)) ` sent))) | s s' a msgs sent. (server_step s a = (s', sent)) \<and> (\<exists>sender. a = UpdateCount pid \<or> a = Receive sender pid Ping \<or> a = ClientJoined pid sender)}
  \<union> {(Buffer s msgs, Send pid rcpt msg, Buffer s (msgs - {(pid,rcpt,msg)})) | s msgs rcpt msg. (pid,rcpt,msg) \<in> msgs}"

definition server_asig :: "'proc \<Rightarrow> ('proc, msg) action signature" where
"server_asig pid =
 ({Receive q pid m | q m. True} \<union> {UpdateCount pid} \<union> {ClientJoined pid newClient | newClient. True},
  {Send pid q m | q m. True},
  {})"

definition Server :: "'proc \<Rightarrow> 'proc set \<Rightarrow> (('proc, msg) action, 'proc server_state) ioa" where
"Server pid clients = (server_asig pid, {Buffer (Count clients 0) {}}, server_trans pid, {}, {})"


(* --- Client --- *)
datatype 'proc cstate = Count (Count_server: 'proc) (Count_curCount: nat)
datatype 'proc client_state = Buffer (client_state_curState: "'proc cstate") (client_state_msgBuffer: "('proc \<times> 'proc \<times> msg) set")

fun client_step:: "'proc cstate \<Rightarrow> ('proc, msg) action \<Rightarrow> 'proc cstate \<times> ('proc \<times> msg) set" where
  \<open>client_step (Count s t) (Receive _ _ (CounterMsg t')) = (Count s (max t t'), {})\<close> |
  \<open>client_step (Count s t) (PingServer _) = (Count s t, {(s, Ping)})\<close> |
  \<open>client_step state _ = (state, {})\<close>

definition client_trans:: "'proc \<Rightarrow> ('proc client_state \<times> ('proc, msg) action \<times> 'proc client_state) set" where
"client_trans pid =
  {(Buffer s msgs, a, Buffer s' (msgs \<union> ((\<lambda>msg. (pid, msg)) ` sent))) | s a s' msgs sent. client_step s a = (s', sent) \<and> (\<exists>s t. a = Receive s pid (CounterMsg t))}
  \<union> {(Buffer s msgs, Send pid rcpt msg, Buffer s (msgs - {(pid,rcpt,msg)})) | s msgs rcpt msg. (pid,rcpt,msg) \<in> msgs}"

definition client_asig:: "'proc \<Rightarrow> ('proc, msg) action signature" where
"client_asig pid =
 ({Receive q pid m | q m. True} \<union> {PingServer pid},
  {Send pid q m| q m. True},
  {})"

definition Client:: "'proc \<Rightarrow> 'proc \<Rightarrow> (('proc, msg) action, 'proc client_state) ioa" where
"Client sid pid = (client_asig pid, {Buffer (Count sid 0) {}}, client_trans pid, {}, {})"

definition Clients:: "'proc \<Rightarrow> 'proc set \<Rightarrow> (('proc, msg) action, 'proc \<Rightarrow> 'proc client_state) ioa" where
"Clients sid clients = set_to_ioa clients (Client sid)"

(* --- Channel --- *)
type_synonym 'proc chan_state = "('proc \<times> 'proc \<times> msg) set"

definition chan_trans :: "('proc chan_state \<times> ('proc, msg) action \<times> 'proc chan_state) set" where
"chan_trans =
  {(M, Send s r m, M \<union> {(s,r,m)}) | M s r m. True}
  \<union> {(M, Receive s r m, M) | M s r m. (s,r,m) \<in> M}"

definition chan_asig :: "('proc, msg) action signature" where
"chan_asig =
 ({Send s r m | s r m. True},
  {Receive s r m | s r m. True},
  {})"

definition Channel :: "(('proc, msg) action, 'proc chan_state) ioa" where
"Channel = (chan_asig, { {} }, chan_trans, {}, {})"


(* --- System Composition --- *)
definition System where
"System server clients = ((Server server clients \<parallel> Channel) \<parallel> Clients server clients)"

end