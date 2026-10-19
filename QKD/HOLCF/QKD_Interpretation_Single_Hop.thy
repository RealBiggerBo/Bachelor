theory QKD_Interpretation_Single_Hop
  imports QKD_inv_qkd_layer_consistent
          HOL.Bit_Operations
begin

(* 1. Define concrete IDs for 2 nodes and their process types *)
datatype concrete_node = Node1 | Node2

datatype concrete_proc = 
    AppProc concrete_node 
  | KmeProc concrete_node 
  | BridgeProc concrete_node 
  | QkdProc concrete_node

(* 2. Define concrete mappings *)
definition c_nodes :: "concrete_node set" where
  "c_nodes = {Node1, Node2}"

definition c_appID :: "concrete_node \<Rightarrow> concrete_proc" where
  "c_appID n = AppProc n"

definition c_kmeID :: "concrete_node \<Rightarrow> concrete_proc" where
  "c_kmeID n = KmeProc n"

definition c_bridgeIDs :: "concrete_node \<Rightarrow> concrete_proc set" where
  "c_bridgeIDs n = {BridgeProc n}"

(*definition c_qkdID :: "concrete_proc \<Rightarrow> concrete_proc" where
  "c_qkdID p = (case p of BridgeProc n \<Rightarrow> QkdProc n | _ \<Rightarrow> p)"*)

definition c_qkdID :: "concrete_proc \<Rightarrow> concrete_proc" where
  "c_qkdID p = (case p of BridgeProc n \<Rightarrow> QkdProc n | _ \<Rightarrow> QkdProc Node1)"

definition c_isMaster :: "concrete_proc \<Rightarrow> bool" where
  "c_isMaster p = (case p of AppProc Node1 \<Rightarrow> True | BridgeProc Node1 \<Rightarrow> True | _ \<Rightarrow> False)"

definition c_appOtherSae :: "concrete_node \<Rightarrow> concrete_proc" where
  "c_appOtherSae n = (if n = Node1 then AppProc Node2 else AppProc Node1)"

definition c_bridgeOtherBridge :: "concrete_proc \<Rightarrow> concrete_proc" where
  "c_bridgeOtherBridge p = (if p = BridgeProc Node1 then BridgeProc Node2 else BridgeProc Node1)"

definition c_bridgeOtherKme :: "concrete_proc \<Rightarrow> concrete_proc" where
  "c_bridgeOtherKme p = (if p = BridgeProc Node1 then KmeProc Node2 else KmeProc Node1)"

definition c_saeToKme :: "concrete_proc \<Rightarrow> concrete_proc" where
  "c_saeToKme p = (case p of AppProc n \<Rightarrow> KmeProc n | BridgeProc n \<Rightarrow> KmeProc n | _ \<Rightarrow> p)"

definition c_route :: "concrete_node \<Rightarrow> concrete_proc \<Rightarrow> concrete_proc" where
  "c_route src dst = c_saeToKme dst"  \<comment> \<open>Direct routing for 2 nodes\<close>

definition c_enc :: "int \<Rightarrow> int \<Rightarrow> int" where "c_enc x y = x + y"
definition c_dec :: "int \<Rightarrow> int \<Rightarrow> int" where "c_dec x y = x - y"

interpretation SingleHop: QKD_Network
  c_nodes c_appID c_kmeID c_bridgeIDs c_qkdID c_isMaster 
  c_appOtherSae c_bridgeOtherBridge c_bridgeOtherKme c_route c_saeToKme 
  c_enc c_dec
proof
  show "\<And>val v1 v2. (c_dec (c_enc val v1) v2 = val) = (v1 = v2)"
    unfolding c_dec_def c_enc_def by fastforce
  show "\<And>n. n \<in> c_nodes \<Longrightarrow> c_bridgeIDs n \<noteq> {}"
    unfolding c_nodes_def c_bridgeIDs_def by simp
  show "inj_on c_appID c_nodes"
    unfolding c_appID_def c_nodes_def by fast
  show "inj_on c_kmeID c_nodes"
    unfolding c_kmeID_def c_nodes_def by fast
  show "inj_on c_qkdID (\<Union> (c_bridgeIDs ` c_nodes))"
    unfolding c_qkdID_def c_bridgeIDs_def c_nodes_def by simp
  show "disjnt (range c_appID) (range c_kmeID) \<and>
    disjnt (range c_appID) (\<Union> (range c_bridgeIDs)) \<and>
    disjnt (range c_appID) (range c_qkdID) \<and>
    disjnt (range c_kmeID) (\<Union> (range c_bridgeIDs)) \<and>
    disjnt (range c_kmeID) (range c_qkdID) \<and> disjnt (\<Union> (range c_bridgeIDs)) (range c_qkdID)"
    unfolding c_appID_def c_kmeID_def c_bridgeIDs_def c_qkdID_def disjnt_def apply auto
      apply (metis concrete_proc.distinct(5) concrete_proc.exhaust concrete_proc.simps(17-20))
     apply (metis concrete_proc.distinct(9) concrete_proc.exhaust concrete_proc.simps(17-20))
    by (metis concrete_proc.distinct(11) concrete_proc.exhaust concrete_proc.simps(17-20))
  show "\<And>n1 n2. n1 \<in> c_nodes \<Longrightarrow> n2 \<in> c_nodes \<Longrightarrow> n1 \<noteq> n2 \<Longrightarrow> disjnt (c_bridgeIDs n1) (c_bridgeIDs n2)"
    unfolding c_nodes_def disjnt_def c_bridgeIDs_def by blast
qed

definition apps where
  \<open>apps app1 app2 = (\<lambda>_. undefined)(Node1 := app1, Node2 := app2)\<close>

definition kmes where
  \<open>kmes kme1 kme2 = (\<lambda>_. undefined)(Node1 := kme1, Node2 := kme2)\<close>

definition bridges where
  \<open>bridges bridge1 bridge2 = (\<lambda>_. undefined)((Node1, BridgeProc Node1) := bridge1, (Node2, BridgeProc Node2) := bridge2)\<close>

definition keyStore_init ::"nat \<rightharpoonup> (int option \<times> concrete_proc \<times> bool \<times> concrete_proc option)"where
  \<open>keyStore_init kid = None\<close>

lemma SingleHop_Starts:
  assumes "app1 = IoaState (App True (AppProc Node2) (KmeProc Node1) {}) {}"
    and "app2 = IoaState (App False (AppProc Node1) (KmeProc Node2) {}) {}"
    and "kme1 = IoaState (Kme keyStore_init (c_route Node1) c_saeToKme) {}"
    and "kme2 = IoaState (Kme keyStore_init (c_route Node2) c_saeToKme) {}"
    and "bridge1 = IoaState (Bridge True (BridgeProc Node2) (KmeProc Node2) (QkdProc Node1) (KmeProc Node1)) {}"
    and "bridge2 = IoaState (Bridge False (BridgeProc Node1) (KmeProc Node1) (QkdProc Node2) (KmeProc Node2)) {}"
  shows "(apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, QKD {} {}, {}) \<in> starts_of SingleHop.System.ioa"
proof -
  have "apps app1 app2 \<in> starts_of SingleHop.apps.ioa"
    unfolding starts_of_set_ioa apps_def c_nodes_def
    unfolding starts_of_def apply simp
    apply(subst assms(1,2))+
    unfolding c_isMaster_def c_appID_def c_appOtherSae_def c_kmeID_def by simp
  moreover have "kmes kme1 kme2 \<in> starts_of SingleHop.kmes.ioa"
    unfolding starts_of_set_ioa kmes_def c_nodes_def
    unfolding starts_of_def apply simp
    apply(subst assms(3,4))+
    unfolding keyStore_init_def by simp
  moreover have "bridges bridge1 bridge2 \<in> starts_of SingleHop.bridges.ioa"
    unfolding starts_of_set_ioa bridges_def c_nodes_def
    unfolding starts_of_def apply simp
    apply(subst assms(5,6))+
    unfolding c_bridgeIDs_def c_isMaster_def c_bridgeOtherBridge_def 
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def by simp
  moreover have "QKD {} {} \<in> starts_of SingleHop.qkd_layer.ioa"
    unfolding starts_of_def by simp
  moreover have "{} \<in> starts_of SingleHop.network.ioa"
    unfolding starts_of_def by simp
  ultimately show ?thesis
    unfolding starts_of_par by force
qed

end