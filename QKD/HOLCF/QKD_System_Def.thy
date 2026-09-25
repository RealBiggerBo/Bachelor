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
  fixes dummy :: "'keyID \<Rightarrow> 'keyVal \<Rightarrow> bool"
  assumes a : "\<And>id val. dummy id val = True"
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

sublocale network: Lossy_Reorder_SetChannel "(appID ` nodes) \<union> (kmeID ` nodes) \<union> (\<Union>(bridgeIDs ` nodes)) \<union> (qkdID ` (\<Union>(bridgeIDs ` nodes)))" .

section Compositions

sublocale bridges: Set_IOA
  "bridgeIDs n"
  "\<lambda>bridgeID. bridge.ioa bridgeID n"
  for n
proof
  show "pairwise_compatible (bridgeIDs n) (\<lambda>bridgeID. bridge.ioa bridgeID n)"
    unfolding pairwise_compatible_def compatible_def asig_projections asig_of_def by auto
  show "\<And>i. i \<in> bridgeIDs n \<Longrightarrow> Automata.IOA (bridge.ioa i n)"
    using bridge.is_ioa by blast
qed

lemma out_bridges:
  shows "\<And>n. out (bridges.ioa n) = \<Union>{out (bridge.ioa bridgeID n) | bridgeID. bridgeID \<in> bridgeIDs n}"
  unfolding outputs_of_set_ioa by blast

lemma int_bridges:
  shows "\<And>n. int (bridges.ioa n) = {}"
  unfolding asig_of_set_ioa
  unfolding family asig_internals_def asig_of_def by auto

sublocale kme_bridges: Par_IOA 
  "kme.ioa n"
  "bridges.ioa n"
  for n
proof
  show "compatible (kme.ioa n) (bridges.ioa n)"
    unfolding compatible_def 
    unfolding int_bridges out_bridges 
    unfolding asig_projections asig_of_def apply auto 
    using kme_neq_bridge by blast
qed

lemma out_kme_bridges:
  shows "\<And>n. out (kme_bridges.ioa n) = out (kme.ioa n) \<union> \<Union> {out (bridge.ioa bridgeID n) |bridgeID. bridgeID \<in> bridgeIDs n}"
  unfolding outputs_of_par out_bridges by fastforce

lemma int_kme_bridges:
  shows "\<And>n. int (kme_bridges.ioa n) = {}"
  unfolding internals_of_par int_bridges
  unfolding family asig_internals_def asig_of_def by auto

sublocale trusted_node: Par_IOA
  "app.ioa n"
  "kme_bridges.ioa n"
  for n
proof
  show "compatible (app.ioa n) (kme_bridges.ioa n)"
    unfolding compatible_def
    unfolding out_kme_bridges int_kme_bridges
    unfolding asig_projections asig_of_def apply auto
     apply (metis disjnt_iff disjoint_ids rangeI)
    using app_neq_bridge by auto
qed

lemma out_trusted_node:
  shows "\<And>n. out (trusted_node.ioa n) = out (app.ioa n) \<union> out (kme.ioa n) \<union> \<Union>{out (bridge.ioa bridgeID n) |bridgeID. bridgeID \<in> bridgeIDs n}"
  unfolding outputs_of_par out_bridges by fast

lemma int_trusted_node:
  shows "\<And>n. int (trusted_node.ioa n) = {}"
  apply(subst internals_of_par)
  unfolding int_kme_bridges
  unfolding asig_projections asig_of_def by force

sublocale trusted_nodes: Set_IOA
  nodes
  "\<lambda>nodeID. trusted_node.ioa nodeID"
proof
  show "pairwise_compatible nodes trusted_node.ioa"
    unfolding pairwise_compatible_def compatible_def
    unfolding int_trusted_node Int_empty_left out_trusted_node
    unfolding asig_projections asig_of_def
    apply auto
            apply (metis inj_app inj_on_contraD)
           apply (metis disjnt_iff disjoint_ids rangeI)
          apply (metis disjnt_iff disjoint_ids rangeI)
         apply (meson inj_kme inj_onD)
    using app_neq_bridge apply auto[1]
    using kme_neq_bridge apply auto[1]
    using app_neq_bridge apply auto[1]
    using kme_neq_bridge apply auto[1]
    using bridge_determines_node by auto
  show "\<And>i. i \<in> nodes \<Longrightarrow> Automata.IOA (trusted_node.ioa i)"
    using trusted_node.is_ioa by fast
qed

lemma out_trusted_nodes:
  "out trusted_nodes.ioa = \<Union>{out (app.ioa n) \<union> out (kme.ioa n) \<union> \<Union>{out (bridge.ioa bridgeID n) |bridgeID. bridgeID \<in> bridgeIDs n} | n. n \<in> nodes}"
  unfolding outputs_of_set_ioa out_trusted_node by blast

lemma int_trusted_nodes:
  shows "int trusted_nodes.ioa = {}"
  unfolding internals_of_set_ioa int_trusted_node by blast

sublocale qkd_layer_network: Par_IOA
  "qkd_layer.ioa"
  "network.ioa"
proof
  show "compatible qkd_layer.ioa network.ioa"
    unfolding compatible_def asig_projections asig_of_def QKD_Layer_locale.asig by auto
qed

sublocale System: Par_IOA
  "trusted_nodes.ioa"
  "qkd_layer_network.ioa"
proof
  show "compatible trusted_nodes.ioa qkd_layer_network.ioa"
    unfolding compatible_def out_trusted_nodes int_trusted_nodes Int_empty_left
    unfolding internals_of_par outputs_of_par
    unfolding asig_projections asig_of_def QKD_Layer_locale.asig apply (simp only: o_apply)
    apply (simp only: prod.sel)
    apply auto
      apply (metis disjnt_iff disjoint_ids rangeI)
     apply (metis disjnt_iff disjoint_ids rangeI)
    by (meson UnionI disjnt_iff disjoint_ids rangeI)
qed

end

end