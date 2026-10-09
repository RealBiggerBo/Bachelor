theory QKD_Interpretation_Line_4Hop
  imports QKD_inv_qkd_layer_consistent
          HOL.Bit_Operations
begin

(* 1. Define concrete IDs for 4 nodes and direction-aware process types *)
datatype concrete_node = Node1 | Node2 | Node3 | Node4

datatype concrete_proc = 
    AppProc concrete_node 
  | KmeProc concrete_node 
  | BridgeProc concrete_node concrete_node 
  | QkdProc concrete_node concrete_node

(* 2. Define concrete mappings *)
definition c_nodes :: "concrete_node set" where
  "c_nodes = {Node1, Node2, Node3, Node4}"

definition c_appID :: "concrete_node \<Rightarrow> concrete_proc" where
  "c_appID n = AppProc n"

definition c_kmeID :: "concrete_node \<Rightarrow> concrete_proc" where
  "c_kmeID n = KmeProc n"

(* Line topology bridge configuration:
   Node1: 1 bridge  -> Node2
   Node2: 2 bridges -> Node1, Node3
   Node3: 2 bridges -> Node2, Node4
   Node4: 1 bridge  -> Node3 *)
definition c_bridgeIDs :: "concrete_node \<Rightarrow> concrete_proc set" where
  "c_bridgeIDs n = (case n of
      Node1 \<Rightarrow> {BridgeProc Node1 Node2}
    | Node2 \<Rightarrow> {BridgeProc Node2 Node1, BridgeProc Node2 Node3}
    | Node3 \<Rightarrow> {BridgeProc Node3 Node2, BridgeProc Node3 Node4}
    | Node4 \<Rightarrow> {BridgeProc Node4 Node3})"

definition c_qkdID :: "concrete_proc \<Rightarrow> concrete_proc" where
  "c_qkdID p = (case p of 
      BridgeProc n1 n2 \<Rightarrow> QkdProc n1 n2 
    | _ \<Rightarrow> QkdProc Node1 Node2)"

(* Master/Slave assignment per link:
   Node1-Node2: Node1 side is Master
   Node2-Node3: Node2 side is Master
   Node3-Node4: Node3 side is Master
   AppProc Node1 is Master for end-to-end key requests *)
definition c_isMaster :: "concrete_proc \<Rightarrow> bool" where
  "c_isMaster p = (case p of 
      AppProc Node1 \<Rightarrow> True 
    | BridgeProc Node1 Node2 \<Rightarrow> True 
    | BridgeProc Node2 Node3 \<Rightarrow> True 
    | BridgeProc Node3 Node4 \<Rightarrow> True 
    | _ \<Rightarrow> False)"

definition c_appOtherSae :: "concrete_node \<Rightarrow> concrete_proc" where
  "c_appOtherSae n = (if n = Node1 then AppProc Node4 else AppProc Node1)"

definition c_bridgeOtherBridge :: "concrete_proc \<Rightarrow> concrete_proc" where
  "c_bridgeOtherBridge p = (case p of
      BridgeProc Node1 Node2 \<Rightarrow> BridgeProc Node2 Node1
    | BridgeProc Node2 Node1 \<Rightarrow> BridgeProc Node1 Node2
    | BridgeProc Node2 Node3 \<Rightarrow> BridgeProc Node3 Node2
    | BridgeProc Node3 Node2 \<Rightarrow> BridgeProc Node2 Node3
    | BridgeProc Node3 Node4 \<Rightarrow> BridgeProc Node4 Node3
    | BridgeProc Node4 Node3 \<Rightarrow> BridgeProc Node3 Node4
    | _ \<Rightarrow> p)"

definition c_bridgeOtherKme :: "concrete_proc \<Rightarrow> concrete_proc" where
  "c_bridgeOtherKme p = (case p of
      BridgeProc Node1 Node2 \<Rightarrow> KmeProc Node2
    | BridgeProc Node2 Node1 \<Rightarrow> KmeProc Node1
    | BridgeProc Node2 Node3 \<Rightarrow> KmeProc Node3
    | BridgeProc Node3 Node2 \<Rightarrow> KmeProc Node2
    | BridgeProc Node3 Node4 \<Rightarrow> KmeProc Node4
    | BridgeProc Node4 Node3 \<Rightarrow> KmeProc Node3
    | _ \<Rightarrow> KmeProc Node1)"

(* Routing along the line topology *)
definition c_route :: "concrete_node \<Rightarrow> concrete_proc \<Rightarrow> concrete_proc" where
  "c_route src dst = (case src of
      Node1 \<Rightarrow> KmeProc Node2
    | Node2 \<Rightarrow> (if dst = AppProc Node1 then KmeProc Node1 else KmeProc Node3)
    | Node3 \<Rightarrow> (if dst = AppProc Node4 then KmeProc Node4 else KmeProc Node2)
    | Node4 \<Rightarrow> KmeProc Node3)"

definition c_saeToKme :: "concrete_proc \<Rightarrow> concrete_proc" where
  "c_saeToKme p = (case p of 
      AppProc n \<Rightarrow> KmeProc n 
    | BridgeProc n1 n2 \<Rightarrow> KmeProc n1 
    | _ \<Rightarrow> p)"

definition c_enc :: "int \<Rightarrow> int \<Rightarrow> int" where "c_enc x y = x + y"
definition c_dec :: "int \<Rightarrow> int \<Rightarrow> int" where "c_dec x y = x - y"

(* 3. Prove locale interpretation *)
interpretation Line4Hop: QKD_Network
  c_nodes c_appID c_kmeID c_bridgeIDs c_qkdID c_isMaster 
  c_appOtherSae c_bridgeOtherBridge c_bridgeOtherKme c_route c_saeToKme 
  c_enc c_dec
proof
  show "\<And>val v1 v2. (c_dec (c_enc val v1) v2 = val) = (v1 = v2)"
    unfolding c_dec_def c_enc_def by fastforce
  show "\<And>n. n \<in> c_nodes \<Longrightarrow> c_bridgeIDs n \<noteq> {}"
    unfolding c_nodes_def c_bridgeIDs_def by (auto split: concrete_node.splits)
  show "inj_on c_appID c_nodes"
    unfolding c_appID_def c_nodes_def by (rule inj_onI, auto split: concrete_node.splits)
  show "inj_on c_kmeID c_nodes"
    unfolding c_kmeID_def c_nodes_def by (rule inj_onI, auto split: concrete_node.splits)
  show "inj_on c_qkdID (\<Union> (c_bridgeIDs ` c_nodes))"
    unfolding c_qkdID_def c_bridgeIDs_def c_nodes_def 
    by (rule inj_onI, auto split: concrete_node.splits concrete_proc.splits)
  show "disjnt (range c_appID) (range c_kmeID) \<and>
        disjnt (range c_appID) (\<Union> (range c_bridgeIDs)) \<and>
        disjnt (range c_appID) (range c_qkdID) \<and>
        disjnt (range c_kmeID) (\<Union> (range c_bridgeIDs)) \<and>
        disjnt (range c_kmeID) (range c_qkdID) \<and> 
        disjnt (\<Union> (range c_bridgeIDs)) (range c_qkdID)"
    unfolding c_appID_def c_kmeID_def c_bridgeIDs_def c_qkdID_def disjnt_def by (auto split: concrete_node.splits concrete_proc.splits)
  show "\<And>n1 n2. n1 \<in> c_nodes \<Longrightarrow> n2 \<in> c_nodes \<Longrightarrow> n1 \<noteq> n2 \<Longrightarrow> disjnt (c_bridgeIDs n1) (c_bridgeIDs n2)"
    unfolding c_nodes_def disjnt_def c_bridgeIDs_def by (auto split: concrete_node.splits)
qed

(* 4. State initializers and initial system trace state *)
definition apps where
  \<open>apps app1 app2 app3 app4 = (\<lambda>_. undefined)
    (Node1 := app1, Node2 := app2, Node3 := app3, Node4 := app4)\<close>

definition kmes where
  \<open>kmes kme1 kme2 kme3 kme4 = (\<lambda>_. undefined)
    (Node1 := kme1, Node2 := kme2, Node3 := kme3, Node4 := kme4)\<close>

definition bridges where
  \<open>bridges b1_2 b2_1 b2_3 b3_2 b3_4 b4_3 = (\<lambda>_. undefined)
    ((Node1, BridgeProc Node1 Node2) := b1_2,
     (Node2, BridgeProc Node2 Node1) := b2_1,
     (Node2, BridgeProc Node2 Node3) := b2_3,
     (Node3, BridgeProc Node3 Node2) := b3_2,
     (Node3, BridgeProc Node3 Node4) := b3_4,
     (Node4, BridgeProc Node4 Node3) := b4_3)\<close>

definition keyStore_init :: "nat \<rightharpoonup> (int option \<times> concrete_proc \<times> bool \<times> concrete_proc option)" where
  \<open>keyStore_init kid = None\<close>

lemma Line4Hop_Starts:
  assumes "app1 = IoaState (App True (AppProc Node4) (KmeProc Node1) {}) {}"
    and "app2 = IoaState (App False (AppProc Node1) (KmeProc Node2) {}) {}"
    and "app3 = IoaState (App False (AppProc Node1) (KmeProc Node3) {}) {}"
    and "app4 = IoaState (App False (AppProc Node1) (KmeProc Node4) {}) {}"
    and "kme1 = IoaState (Kme keyStore_init (c_route Node1) c_saeToKme) {}"
    and "kme2 = IoaState (Kme keyStore_init (c_route Node2) c_saeToKme) {}"
    and "kme3 = IoaState (Kme keyStore_init (c_route Node3) c_saeToKme) {}"
    and "kme4 = IoaState (Kme keyStore_init (c_route Node4) c_saeToKme) {}"
    and "b1_2 = IoaState (Bridge True (BridgeProc Node2 Node1) (KmeProc Node2) (QkdProc Node1 Node2) (KmeProc Node1)) {}"
    and "b2_1 = IoaState (Bridge False (BridgeProc Node1 Node2) (KmeProc Node1) (QkdProc Node2 Node1) (KmeProc Node2)) {}"
    and "b2_3 = IoaState (Bridge True (BridgeProc Node3 Node2) (KmeProc Node3) (QkdProc Node2 Node3) (KmeProc Node2)) {}"
    and "b3_2 = IoaState (Bridge False (BridgeProc Node2 Node3) (KmeProc Node2) (QkdProc Node3 Node2) (KmeProc Node3)) {}"
    and "b3_4 = IoaState (Bridge True (BridgeProc Node4 Node3) (KmeProc Node4) (QkdProc Node3 Node4) (KmeProc Node3)) {}"
    and "b4_3 = IoaState (Bridge False (BridgeProc Node3 Node4) (KmeProc Node3) (QkdProc Node4 Node3) (KmeProc Node4)) {}"
  shows "(apps app1 app2 app3 app4, 
          kmes kme1 kme2 kme3 kme4, 
          bridges b1_2 b2_1 b2_3 b3_2 b3_4 b4_3, 
          QKD {} {}, {}) \<in> starts_of Line4Hop.System.ioa"
proof -
  have "apps app1 app2 app3 app4 \<in> starts_of Line4Hop.apps.ioa"
    unfolding starts_of_set_ioa apps_def c_nodes_def
    unfolding starts_of_def apply simp
    apply(subst assms(1,2,3,4))+
    unfolding c_isMaster_def c_appID_def c_appOtherSae_def c_kmeID_def by simp
  moreover have "kmes kme1 kme2 kme3 kme4 \<in> starts_of Line4Hop.kmes.ioa"
    unfolding starts_of_set_ioa kmes_def c_nodes_def
    unfolding starts_of_def apply simp
    apply(subst assms(5,6,7,8))+
    unfolding keyStore_init_def by simp
  moreover have "bridges b1_2 b2_1 b2_3 b3_2 b3_4 b4_3 \<in> starts_of Line4Hop.bridges.ioa"
    unfolding starts_of_set_ioa bridges_def c_nodes_def
    unfolding starts_of_def apply simp
    apply(subst assms(9,10,11,12,13,14))+
    unfolding c_bridgeIDs_def c_isMaster_def c_bridgeOtherBridge_def 
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def by simp
  moreover have "QKD {} {} \<in> starts_of Line4Hop.qkd_layer.ioa"
    unfolding starts_of_def by simp
  moreover have "{} \<in> starts_of Line4Hop.network.ioa"
    unfolding starts_of_def by simp
  ultimately show ?thesis
    unfolding starts_of_par by force
qed

end