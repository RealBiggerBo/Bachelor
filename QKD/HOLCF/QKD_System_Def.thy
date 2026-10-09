theory QKD_System_Def
  imports Automata_Set_IOA Automata_Par_IOA 
          Automata_Par_Helpers
          QKD_App 
          QKD_KME 
          QKD_ETSI_Bridge 
          QKD_QKD_Layer
          QKD_Channel_Definitions_IOA
begin

(*
Symmetry of connections: If bridge A connects to bridge B, B must connect to A.
Future assume: bridgeOtherBridge (bridgeOtherBridge b) = b

No self-loops: A bridge doesn't connect to itself.
Future assume: bridgeOtherBridge b \<noteq> b

Master/Slave pairings: In ETSI QKD, if one side of a link is the Master, the other must be the Slave.
Future assume: isMaster b \<longleftrightarrow> \<not> isMaster (bridgeOtherBridge b)

Closed Network: Bridges only point to other active bridges in the network.
Future assume: b \<in> \<Union>(bridgeID  nodes) \<Longrightarrow> bridgeOtherBridge b \<in> \<Union>(bridgeID  nodes)
*)

locale QKD_Network =
  fixes nodes :: "'nodeID set"
    and appID :: "'nodeID \<Rightarrow> 'proc"
    and kmeID :: "'nodeID \<Rightarrow> 'proc"
    and bridgeIDs :: "'nodeID \<Rightarrow> 'proc set"
    and qkdID :: "'proc \<Rightarrow> 'proc"
    and isMaster :: "'proc \<Rightarrow> bool"
    and appOtherSae :: "'nodeID \<Rightarrow> 'proc"
    and bridgeOtherBridge:: "'proc \<Rightarrow> 'proc"
    and bridgeOtherKme :: "'proc \<Rightarrow> 'proc"
    and route :: "'nodeID \<Rightarrow> 'proc \<Rightarrow> 'proc"
    and saeToKme :: "'proc \<Rightarrow> 'proc"
    and enc :: "'keyVal \<Rightarrow> 'keyVal \<Rightarrow> 'keyVal"
    and dec :: "'keyVal \<Rightarrow> 'keyVal \<Rightarrow> 'keyVal"
  assumes cipher_correctness: "\<And>val v1 v2. dec (enc val v1) v2 = val \<longleftrightarrow> v1 = v2"
    and bridge_exists: "\<And>n. n \<in> nodes \<Longrightarrow> bridgeIDs n \<noteq> {}"
    and inj_app: "inj_on appID nodes"
    and inj_kme: "inj_on kmeID nodes"
    and inj_qkd: "inj_on qkdID (\<Union>(bridgeIDs ` nodes))"
    (* To compose IOAs, output signatures must be disjoint. 
       Ensure component ID ranges do not overlap. *)
    and disjoint_ids: "disjnt (range appID) (range kmeID) \<and>
                       disjnt (range appID) (\<Union>(range bridgeIDs)) \<and>
                       disjnt (range appID) (range qkdID) \<and>
                       disjnt (range kmeID) (\<Union>(range bridgeIDs)) \<and>
                       disjnt (range kmeID) (range qkdID) \<and>
                       disjnt (\<Union>(range bridgeIDs)) (range qkdID)"
    and disjoint_node_bridges: "\<And>n1 n2. \<lbrakk>n1 \<in> nodes; n2 \<in> nodes; n1 \<noteq> n2\<rbrakk> \<Longrightarrow> 
                                   disjnt (bridgeIDs n1) (bridgeIDs n2)"
begin

section SanityChecks

lemma bridge_exists_:
  "\<And>n. n \<in> nodes \<Longrightarrow> (\<exists>id. id \<in> (bridgeIDs n))"
  using bridge_exists by blast

lemma qkd_unique_external_nodes:
  "\<And>b1 b2 n1 n2. \<lbrakk>n1 \<in> nodes; n2 \<in> nodes; n1 \<noteq> n2; b1 \<in> (bridgeIDs n1); b2 \<in> (bridgeIDs n2)\<rbrakk> \<Longrightarrow> qkdID b1 \<noteq> qkdID b2"
  by (smt (verit, best) UnionI disjnt_iff disjoint_node_bridges image_eqI inj_on_contraD inj_qkd)

lemma qkd_unique_internal_nodes: 
  "\<And>n b1 b2. \<lbrakk>n \<in> nodes; b1 \<in> bridgeIDs n; b2 \<in> bridgeIDs n; b1 \<noteq> b2\<rbrakk> \<Longrightarrow> qkdID b1 \<noteq> qkdID b2"
  by (meson UnionI imageI inj_onD inj_qkd)

lemma bridge_determines_node:
  "\<And>n1 n2 b. \<lbrakk>n1 \<in> nodes; n2 \<in> nodes; b \<in> bridgeIDs n1; b \<in> bridgeIDs n2\<rbrakk> \<Longrightarrow> n1 = n2"
  using disjoint_node_bridges unfolding disjnt_iff by blast

lemma app_neq_bridge:
  "\<And>n1 n2 b. b \<in> bridgeIDs n2 \<Longrightarrow> appID n1 \<noteq> b"
  using disjoint_ids unfolding disjnt_iff by auto

lemma kme_neq_bridge:
  "\<And>n1 n2 b. b \<in> bridgeIDs n2 \<Longrightarrow> kmeID n1 \<noteq> b"
  using disjoint_ids unfolding disjnt_iff by auto

lemma bridge_qkd_bij:
  "bij_betw qkdID (\<Union>(bridgeIDs ` nodes)) (qkdID ` (\<Union>(bridgeIDs ` nodes)))"
  unfolding bij_betw_def using inj_qkd by auto

section BaseNodes

sublocale app: App_locale "appID n" "isMaster (appID n)" "appOtherSae n" "kmeID n"
  for n .

sublocale kme: Kme_locale "kmeID n" "route n" "saeToKme" "enc" "dec"
  for n
proof
  show "\<And>val v1 v2. (dec (enc val v1) v2 = val) = (v1 = v2)"
    using cipher_correctness by simp
qed

sublocale bridge: ETSI_Bridge_locale "bridgeID" "isMaster bridgeID" "bridgeOtherBridge bridgeID" "bridgeOtherKme bridgeID" "qkdID bridgeID" "kmeID n"
  for bridgeID n .

sublocale qkd_layer: QKD_Layer_locale "qkdID ` (\<Union>(bridgeIDs ` nodes))" .

sublocale network: Lossy_Reorder_SetChannel .

section Set_Compositions

sublocale apps: Set_IOA
  "nodes"
  "\<lambda>nodeID. app.ioa nodeID"
proof
  show "pairwise_compatible nodes app.ioa"
    unfolding pairwise_compatible_def compatible_def asig_projections asig_of_def
    using inj_app 
    unfolding inj_on_def by (simp;fast)
  show "\<And>i. i \<in> nodes \<Longrightarrow> Automata.IOA (app.ioa i)"
    using app.is_ioa by fast
qed

sublocale kmes: Set_IOA
  "nodes"
  "\<lambda>nodeID. kme.ioa nodeID"
proof
  show "pairwise_compatible nodes kme.ioa"
    unfolding pairwise_compatible_def compatible_def asig_projections asig_of_def
    using inj_kme 
    unfolding inj_on_def by (simp;fast)
  show "\<And>i. i \<in> nodes \<Longrightarrow> Automata.IOA (kme.ioa i)"
    using kme.is_ioa by fast
qed

sublocale bridges: Set_IOA
  "Sigma nodes bridgeIDs"
  "\<lambda>(nodeID, bridgeID). bridge.ioa bridgeID nodeID"
proof
  show "pairwise_compatible (Sigma nodes bridgeIDs) (\<lambda>(nodeID, bridgeID). bridge.ioa bridgeID nodeID)"
    unfolding pairwise_compatible_def compatible_def asig_projections asig_of_def apply auto
    using disjoint_node_bridges unfolding disjnt_iff by metis
  show "\<And>i. i \<in> Sigma nodes bridgeIDs \<Longrightarrow> Automata.IOA (case i of (nodeID, bridgeID) \<Rightarrow> bridge.ioa bridgeID nodeID)"
    using bridge.is_ioa by fast
qed

section ParCompositions

sublocale qkd_layer_network: Par_IOA
  "qkd_layer.ioa"
  "network.ioa"
proof
  show "compatible qkd_layer.ioa network.ioa"
    unfolding compatible_def asig_projections asig_of_def QKD_Layer_locale.asig by auto
qed

sublocale bridges_qkd_layer_network: Par_IOA
  "bridges.ioa"
  "qkd_layer_network.ioa"
proof
  show "compatible bridges.ioa qkd_layer_network.ioa"
    apply (subst compatibleParR)
    unfolding compatible_def
    unfolding outputs_of_set_ioa internals_of_set_ioa actions_of_set_ioa inputs_of_set_ioa
    unfolding asig_projections asig_of_def qkd_layer.asig apply (simp split: if_splits)
    apply auto
    by (meson UnionI disjnt_iff disjoint_ids rangeI)
qed

sublocale kmes_bridges_qkd_layer_network: Par_IOA
  "kmes.ioa"
  "bridges_qkd_layer_network.ioa"
proof
  show "compatible kmes.ioa bridges_qkd_layer_network.ioa"
    apply (subst compatibleParR)+
    unfolding compatible_def
    unfolding outputs_of_set_ioa internals_of_set_ioa actions_of_set_ioa inputs_of_set_ioa
    unfolding asig_projections asig_of_def qkd_layer.asig apply (simp split: if_splits)
    apply auto
    using kme_neq_bridge apply auto[1]
    by (metis disjnt_iff disjoint_ids rangeI)
qed

sublocale System: Par_IOA
  "apps.ioa"
  "kmes_bridges_qkd_layer_network.ioa"
proof
  show "compatible apps.ioa kmes_bridges_qkd_layer_network.ioa"
    apply (subst compatibleParR)+
    unfolding compatible_def
    unfolding outputs_of_set_ioa internals_of_set_ioa actions_of_set_ioa inputs_of_set_ioa
    unfolding asig_projections asig_of_def qkd_layer.asig apply (simp split: if_splits)
    apply auto
      apply (metis disjnt_iff disjoint_ids rangeI)
    using app_neq_bridge apply auto[1]
    by (metis disjnt_iff disjoint_ids rangeI)
qed

end

end