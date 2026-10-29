theory Automata_System_Def
  imports Automata_Network_DIOA Automata_Set_IOA Automata_Par_IOA Automata_Channel_IOA
begin

locale Global_Network =
  fixes server :: "'proc"
    and clients :: "'proc set"
  assumes server_not_client: "server \<notin> clients"
begin

section Server

fun server_step:: "'proc sstate \<Rightarrow> ('proc, msg) action \<Rightarrow> 'proc sstate \<times> ('proc \<times> msg) set" where
  \<open>server_step (sstate.Count cls counter) (UpdateCount _) = (sstate.Count cls (counter + 1), {(client, CounterMsg (counter + 1)) | client. client \<in> cls})\<close> |
  \<open>server_step (sstate.Count cls counter) (ClientJoined _ newClient) = (sstate.Count (cls \<union> {newClient}) counter, {})\<close> |
  \<open>server_step state (Receive client _ Ping) = (state, {(client, Pong)})\<close> |
  \<open>server_step state _ = (state, {})\<close>

sublocale Server: Network_DIOA
  server
  "{UpdateCount server} \<union> {ClientJoined server newClient | newClient. True}"
  "(sstate.Count clients 0)"
  server_step
proof
  show "\<forall>rcpt msg. Send server rcpt msg \<notin> {UpdateCount server} \<union> {ClientJoined server newClient |newClient. True}"
    by simp
qed



section Clients

fun client_step:: "'proc cstate \<Rightarrow> ('proc, msg) action \<Rightarrow> 'proc cstate \<times> ('proc \<times> msg) set" where
  \<open>client_step (cstate.Count s t) (Receive _ _ (CounterMsg t')) = (cstate.Count s (max t t'), {})\<close> |
  \<open>client_step (cstate.Count s t) (PingServer _) = (cstate.Count s t, {(s, Ping)})\<close> |
  \<open>client_step state _ = (state, {})\<close>

sublocale Client: Network_DIOA
  pid
  "{PingServer pid}"
  "(cstate.Count sid 0)"
  client_step
  for sid pid
proof
  show "\<forall>rcpt msg. Send pid rcpt msg \<notin> {PingServer pid}"
    by simp
qed

sublocale Clients: Set_IOA
  clients
  "\<lambda>id. Client.ioa id server"
  rewrites "int Clients.ioa = {}"
  apply(unfold_locales)
proof -
  show "pairwise_compatible clients (\<lambda>id. Client.ioa id server)"
    unfolding pairwise_compatible_def compatible_def asig_projections apply simp
    unfolding asig_of_def by auto
  show "\<And>i. i \<in> clients \<Longrightarrow> Automata.IOA (Client.ioa i server)"
    using Client.is_ioa by simp
  show "Automata.int (set_to_ioa clients (\<lambda>id. Client.ioa id server)) = {}"
    sorry
qed



section Channels

sublocale Fifo_Channel: DirectedChannel_IOA
  pid_sender
  pid_rcpt
  "[]"
  "\<lambda>msgs msg. msg#msgs"
  "\<lambda>msgs msg. tl msgs"
  "\<lambda>msgs msg. (if \<exists>x xs. msgs = x#xs then hd msgs = msg else False)"
  for pid_sender pid_rcpt
  done

sublocale Lossy_Reorder_Channel: DirectedChannel_IOA
  pid_sender  
  pid_rcpt
  "{}"
  "\<lambda>s m. s \<union> {m}"
  "\<lambda>s m. s"
  "\<lambda>s m. m \<in> s"
  for pid_sender pid_rcpt
  done

  (* 1. Server-to-Client Channels *)
sublocale Channels_S2C: Set_IOA 
  "{server} \<times> clients" 
  "\<lambda>(src, dst). Fifo_Channel.ioa src dst"
  rewrites inp_eq_s2c:"inp (set_to_ioa ({server} \<times> clients) (\<lambda>(src, dst). Fifo_Channel.ioa src dst))= {Send server r m| r m. r \<in> clients}"
    and out_eq_s2c:"out (set_to_ioa ({server} \<times> clients) (\<lambda>(src, dst). Fifo_Channel.ioa src dst))= {Receive server r m| r m. r \<in> clients}"
    and int_eq_s2c:"int (set_to_ioa ({server} \<times> clients) (\<lambda>(src, dst). Fifo_Channel.ioa src dst)) = {}"
  apply (unfold_locales)
proof -
  show "pairwise_compatible ({server} \<times> clients) (\<lambda>(src, dst). Fifo_Channel.ioa src dst)" 
    unfolding pairwise_compatible_def compatible_def apply auto
    unfolding asig_projections asig_of_def apply simp
      apply blast
    by auto
  show "\<And>i. i \<in> {server} \<times> clients \<Longrightarrow> Automata.IOA (case i of (src, dst) \<Rightarrow> Fifo_Channel.ioa src dst)"
    by (metis (mono_tags, lifting) Fifo_Channel.IOA_axioms IOA.is_ioa case_prod_conv surj_pair)
  show "inp (set_to_ioa ({server} \<times> clients) (\<lambda>(src, dst). Fifo_Channel.ioa src dst)) = {Send server r m |r m. r \<in> clients}"
    unfolding asig_projections asig_of_def set_to_ioa_def family by force
  show "out (set_to_ioa ({server} \<times> clients) (\<lambda>(src, dst). Fifo_Channel.ioa src dst)) = {Receive server r m |r m. r \<in> clients}"
    unfolding asig_projections asig_of_def set_to_ioa_def family by force
  show "int (set_to_ioa ({server} \<times> clients) (\<lambda>(src, dst). Fifo_Channel.ioa src dst)) = {}"
    unfolding asig_projections asig_of_def set_to_ioa_def family by force
qed

  (* 2. Client-to-Server Channels *)
sublocale Channels_C2S: Set_IOA
  "clients \<times> {server}"
  "\<lambda>(src, dst). Fifo_Channel.ioa src dst"
  rewrites inp_eq_c2s:"inp (set_to_ioa (clients \<times> {server}) (\<lambda>(src, dst). Fifo_Channel.ioa src dst))= {Send s server m| s m. s \<in> clients}"
    and out_eq_c2s:"out (set_to_ioa (clients \<times> {server}) (\<lambda>(src, dst). Fifo_Channel.ioa src dst))= {Receive s server m| s m. s \<in> clients}"
    and int_eq_c2s:"int (set_to_ioa (clients \<times> {server}) (\<lambda>(src, dst). Fifo_Channel.ioa src dst)) = {}"
  apply(unfold_locales)
proof -
  show "pairwise_compatible (clients \<times> {server}) (\<lambda>(src, dst). Fifo_Channel.ioa src dst)" 
    unfolding pairwise_compatible_def compatible_def apply auto
    unfolding asig_projections asig_of_def apply simp
      apply blast
    by auto  
  show "\<And>i. i \<in> clients \<times> {server} \<Longrightarrow> Automata.IOA (case i of (src, dst) \<Rightarrow> Fifo_Channel.ioa src dst)" 
    by (metis (mono_tags, lifting) Fifo_Channel.IOA_axioms IOA.is_ioa case_prod_conv surj_pair)
  show "inp (set_to_ioa (clients \<times> {server}) (\<lambda>(src, dst). Fifo_Channel.ioa src dst))= {Send s server m| s m. s \<in> clients}"
    unfolding asig_projections asig_of_def set_to_ioa_def family by force
  show "out (set_to_ioa (clients \<times> {server}) (\<lambda>(src, dst). Fifo_Channel.ioa src dst))= {Receive s server m| s m. s \<in> clients}"
    unfolding asig_projections asig_of_def set_to_ioa_def family by force
  show "int (set_to_ioa (clients \<times> {server}) (\<lambda>(src, dst). Fifo_Channel.ioa src dst)) = {}"
    unfolding asig_projections asig_of_def set_to_ioa_def family by force
qed



section Pars

  (* 3. Compose Channels via Par_IOA *)
sublocale Channels: Par_IOA 
  "Channels_S2C.ioa"
  "Channels_C2S.ioa"
  rewrites inp_eq_cs:"inp (Channels_S2C.ioa \<parallel> Channels_C2S.ioa) = {Send s r m| s r m. (s \<in> clients \<and> r = server) \<or> (s = server \<and> r \<in> clients)}"
    and out_eq_cs:"out (Channels_S2C.ioa \<parallel> Channels_C2S.ioa) = {Receive s r m| s r m. (s \<in> clients \<and> r = server) \<or> (s = server \<and> r \<in> clients)}"
    and int_eq_cs:"int (Channels_S2C.ioa \<parallel> Channels_C2S.ioa) = {}"
     apply (unfold_locales)
proof -
  show "compatible Channels_S2C.ioa Channels_C2S.ioa"
    using server_not_client
    unfolding compatible_def apply simp
    unfolding asig_projections family asig_of_def by auto
  show "inp (Channels_S2C.ioa \<parallel> Channels_C2S.ioa) = {Send s r m| s r m. (s \<in> clients \<and> r = server) \<or> (s = server \<and> r \<in> clients)}"
    sorry
  show "out (Channels_S2C.ioa \<parallel> Channels_C2S.ioa) = {Receive s r m| s r m. (s \<in> clients \<and> r = server) \<or> (s = server \<and> r \<in> clients)}"
    sorry
  show "int (Channels_S2C.ioa \<parallel> Channels_C2S.ioa) = {}"
    sorry
qed
    
    


  (* 4. Compose Server with the Network Channels *)
sublocale Server_Channels: Par_IOA 
    "Server.ioa" 
    "Channels.ioa"
  proof unfold_locales
    show "compatible Server.ioa Channels.ioa"
      unfolding compatible_def asig_projections asig_of_def par_def apply simp
      unfolding asig_comp_def set_to_ioa_def apply simp
      unfolding asig_projections family apply simp
      unfolding asig_of_def by auto
  qed

(* 5. Compose (Server + Channels) with the Clients to form the Final System *)
sublocale System: Par_IOA 
    "Server_Channels.ioa" 
    "Clients.ioa"
  proof unfold_locales
    show "compatible Server_Channels.ioa Clients.ioa"
      using server_not_client
      unfolding compatible_def asig_projections asig_of_def par_def apply simp
      unfolding asig_comp_def set_to_ioa_def apply simp
      unfolding asig_projections family apply simp
      unfolding asig_of_def by auto
 qed

definition System2 where
  \<open>System2 \<equiv> (Server.ioa \<parallel> (Channels_S2C.ioa \<parallel> Channels_C2S.ioa)) \<parallel> Clients.ioa\<close>

lemma "Automata.IOA System.ioa"
  using System.is_ioa by simp

end

end