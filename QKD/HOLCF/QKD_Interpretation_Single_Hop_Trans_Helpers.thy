theory QKD_Interpretation_Single_Hop_Trans_Helpers
  imports QKD_Interpretation_Single_Hop
begin

lemma trusted_node_act_distinct:
  assumes "a \<in> act (SingleHop.trusted_node.ioa i)"
    and "a \<in> act (SingleHop.trusted_node.ioa i')"
    and "i \<in> c_nodes \<and> i' \<in> c_nodes"
  shows "i = i'"
  using assms
  unfolding actions_of_par actions_of_set_ioa
  unfolding actions_def asig_projections asig_of_def apply simp
  unfolding c_bridgeIDs_def c_isMaster_def c_appID_def apply simp
  unfolding c_kmeID_def c_nodes_def by auto

lemma bridge_act_distinct:
  assumes "a \<in> act (SingleHop.bridge.ioa b i)"
    and "a \<in> act (SingleHop.bridge.ioa b' i')"
    and "i \<in> c_nodes \<and> i' \<in> c_nodes \<and> b \<in> c_bridgeIDs i \<and> b' \<in> c_bridgeIDs i'"
  shows "i = i' \<and> b = b'"
  using assms
  unfolding actions_of_par actions_of_set_ioa
  unfolding actions_def asig_projections asig_of_def apply simp
  unfolding c_bridgeIDs_def c_isMaster_def c_appID_def apply simp
  unfolding c_kmeID_def c_nodes_def by auto

lemma tns_qkd_layer_act_distinct:
  shows "act SingleHop.trusted_nodes.ioa \<inter> act SingleHop.qkd_layer.ioa = {}"
  unfolding actions_of_par actions_of_set_ioa c_nodes_def
  unfolding actions_def asig_projections asig_of_def QKD_Layer_locale.asig apply simp
  unfolding c_appID_def c_kmeID_def c_isMaster_def c_bridgeIDs_def c_qkdID_def by auto

lemma app_kme_bridges_act_distinct:
  assumes "i \<in> c_nodes"
  shows "act (SingleHop.app.ioa i) \<inter> act (SingleHop.kme_bridges.ioa i) = {}"
  unfolding actions_of_par actions_of_set_ioa c_nodes_def
  unfolding actions_def asig_projections asig_of_def QKD_Layer_locale.asig apply simp
  unfolding c_appID_def c_kmeID_def c_isMaster_def c_bridgeIDs_def c_qkdID_def by auto

lemma kme_bridges_act_distinct:
  assumes "i \<in> c_nodes"
  shows "act (SingleHop.kme.ioa i) \<inter> act (SingleHop.bridges.ioa i) = {}"
  unfolding actions_of_par actions_of_set_ioa c_nodes_def
  unfolding actions_def asig_projections asig_of_def QKD_Layer_locale.asig apply simp
  unfolding c_appID_def c_kmeID_def c_isMaster_def c_bridgeIDs_def c_qkdID_def by auto

lemma tns_network_acts_inter:
  assumes "a \<in> act SingleHop.network.ioa"
  assumes "a \<in> act SingleHop.trusted_nodes.ioa"
  shows "\<exists>sender rcpt msg. a = Send sender rcpt msg \<or> a = Receive sender rcpt msg"
proof -
  have "act SingleHop.network.ioa \<inter> act (SingleHop.trusted_nodes.ioa) \<subseteq> {m. \<exists>sender rcpt msg. (m = Send sender rcpt msg) \<or> (m = Receive sender rcpt msg)}"
    unfolding actions_of_par actions_of_set_ioa
    unfolding actions_def asig_projections asig_of_def apply simp
    unfolding c_appID_def c_nodes_def c_kmeID_def c_qkdID_def c_bridgeIDs_def c_isMaster_def apply simp
    by blast
  then show ?thesis
    using assms by blast
qed

lemma trans_in_app_no_netw:
  assumes "\<forall>sender receiver msg. a \<noteq> Send sender receiver msg"
    and "\<forall>sender receiver msg. a \<noteq> Receive sender receiver msg"
    and "s = (tn app1 kme1 app2 kme2 bridge1 bridge2, qkd, msgs)"
    and "t = (tn app1' kme1 app2' kme2 bridge1 bridge2, qkd, msgs)"
    and "i \<in> c_nodes"
    and app_trans: "(fst (fst s i), a, fst (fst t i)) \<in> trans_of (SingleHop.app.ioa i)"
    and "(i = Node1 \<longrightarrow> app2 = app2') \<and> (i = Node2 \<longrightarrow> app1 = app1')"
  shows "(s,a,t) \<in> trans_of SingleHop.System.ioa"
proof -
  have a_act_app: "a \<in> act (SingleHop.app.ioa i)"
    using app_trans SingleHop.app.is_ioa[of i] unfolding Automata.IOA_def is_trans_of_def by fastforce
  have a_in_tn: "a \<in> act (SingleHop.trusted_node.ioa i)"
    by (intro par_actL a_act_app)
  have a_in_tns: "a \<in> act SingleHop.trusted_nodes.ioa"
    unfolding actions_of_set_ioa using assms(5) a_in_tn by fast
  show ?thesis
  proof (rule trans_par_inductFst)
    show "a \<in> act SingleHop.trusted_nodes.ioa" 
      by (rule a_in_tns)
    show "fst s \<midarrow>a\<midarrow>SingleHop.trusted_nodes.ioa\<rightarrow> fst t"
    proof (rule trans_set_ioa_induct[of i])
      show "i \<in> c_nodes" 
        by (rule assms(5))
      show "a \<in> act (SingleHop.trusted_node.ioa i)" 
        by (rule a_in_tn)
      show "fst s i \<midarrow>a\<midarrow>SingleHop.trusted_node.ioa i\<rightarrow> fst t i"
      proof (rule trans_par_inductFst)
        show "a \<in> act (SingleHop.app.ioa i)" 
          by (rule a_act_app)
        show "fst (fst s i) \<midarrow>a\<midarrow>SingleHop.app.ioa i\<rightarrow> fst (fst t i)" 
          by (rule app_trans)
        show "a \<notin> act (SingleHop.kme_bridges.ioa i)"
          using a_act_app assms(5) app_kme_bridges_act_distinct by fast
        show "snd (fst s i) = snd (fst t i)"
          using a_act_app assms
          unfolding actions_of_par actions_of_set_ioa actions_def asig_projections asig_of_def 
                    c_isMaster_def c_appID_def c_bridgeIDs_def c_kmeID_def c_nodes_def tn_def bridge_def
          by (auto split: if_splits)
      qed
      show "\<forall>ia\<in>c_nodes. ia \<noteq> i \<longrightarrow> a \<notin> act (SingleHop.trusted_node.ioa ia)"
        using trusted_node_act_distinct a_in_tn assms(5) by blast 
      show "fst t = (fst s)(i := fst t i)"
        using assms by (auto simp: tn_def c_nodes_def)
    qed
    show "a \<notin> act SingleHop.qkd_layer_network.ioa"
    proof (rule no_par_act)
      show "a \<notin> act SingleHop.qkd_layer.ioa"
        using a_in_tns tns_qkd_layer_act_distinct by blast
      show "a \<notin> act SingleHop.network.ioa"
        using a_in_tns tns_network_acts_inter assms(1,2) by blast
    qed
    show "snd s = snd t"
      using assms(3,4) by simp
  qed
qed

lemma trans_in_kme_no_netw:
  assumes "\<forall>sender receiver msg. a \<noteq> Send sender receiver msg"
    and "\<forall>sender receiver msg. a \<noteq> Receive sender receiver msg"
    and "s = (tn app1 kme1 app2 kme2 bridge1 bridge2, qkd, msgs)"
    and "t = (tn app1 kme1' app2 kme2' bridge1 bridge2, qkd, msgs)"
    and "i \<in> c_nodes"
    and kme_trans: "(fst (snd (fst s i)), a, fst (snd (fst t i))) \<in> trans_of (SingleHop.kme.ioa i)"
    and "(i = Node1 \<longrightarrow> kme2 = kme2') \<and> (i = Node2 \<longrightarrow> kme1 = kme1')"
  shows "(s,a,t) \<in> trans_of SingleHop.System.ioa"
proof -
  have a_act_kme: "a \<in> act (SingleHop.kme.ioa i)"
    using kme_trans SingleHop.kme.is_ioa[of i] unfolding Automata.IOA_def is_trans_of_def by fastforce
  have a_in_tn: "a \<in> act (SingleHop.trusted_node.ioa i)"
    by (intro par_actR par_actL a_act_kme)
  have a_in_tns: "a \<in> act SingleHop.trusted_nodes.ioa"
    unfolding actions_of_set_ioa using assms(5) a_in_tn by fast
  show ?thesis
  proof (rule trans_par_inductFst)
    show "a \<in> act SingleHop.trusted_nodes.ioa" 
      by (rule a_in_tns)
    show "fst s \<midarrow>a\<midarrow>SingleHop.trusted_nodes.ioa\<rightarrow> fst t"
    proof (rule trans_set_ioa_induct[of i])
      show "i \<in> c_nodes" 
        by (rule assms(5))
      show "a \<in> act (SingleHop.trusted_node.ioa i)" 
        by (rule a_in_tn)
      show "fst s i \<midarrow>a\<midarrow>SingleHop.trusted_node.ioa i\<rightarrow> fst t i"
      proof (rule trans_par_inductSnd)
        show "a \<notin> act (SingleHop.app.ioa i)"
          using a_act_kme assms(5) app_kme_bridges_act_distinct
          unfolding actions_of_par by blast
        show "a \<in> act (SingleHop.kme_bridges.ioa i)"
          using a_act_kme
          unfolding actions_of_par by blast
        show "snd (fst s i) \<midarrow>a\<midarrow>SingleHop.kme_bridges.ioa i\<rightarrow> snd (fst t i)" 
        proof (rule trans_par_inductFst)
          show "a \<in> act (SingleHop.kme.ioa i)"
            using a_act_kme .
          show "fst (snd (fst s i)) \<midarrow>a\<midarrow>SingleHop.kme.ioa i\<rightarrow> fst (snd (fst t i))"
            using assms(6) .
          show "a \<notin> act (SingleHop.bridges.ioa i)"
            using kme_bridges_act_distinct a_act_kme assms(5) by fast
          show "snd (snd (fst s i)) = snd (snd (fst t i))"
            by(simp only: assms tn_def; simp)
        qed
        show "fst (fst s i) = fst (fst t i)"
          using a_act_kme assms
          unfolding actions_of_par actions_of_set_ioa actions_def asig_projections asig_of_def 
                    c_isMaster_def c_appID_def c_bridgeIDs_def c_kmeID_def c_nodes_def tn_def bridge_def
          by (auto split: if_splits)
      qed
      show "\<forall>ia\<in>c_nodes. ia \<noteq> i \<longrightarrow> a \<notin> act (SingleHop.trusted_node.ioa ia)"
        using trusted_node_act_distinct a_in_tn assms(5) by blast 
      show "fst t = (fst s)(i := fst t i)"
        using assms by (auto simp: tn_def c_nodes_def)
    qed
    show "a \<notin> act SingleHop.qkd_layer_network.ioa"
    proof (rule no_par_act)
      show "a \<notin> act SingleHop.qkd_layer.ioa"
        using a_in_tns tns_qkd_layer_act_distinct by blast
      show "a \<notin> act SingleHop.network.ioa"
        using a_in_tns tns_network_acts_inter assms(1,2) by blast
    qed
    show "snd s = snd t"
      using assms(3,4) by simp
  qed
qed

lemma trans_in_bridge_no_netw:
  assumes "\<forall>sender receiver msg. a \<noteq> Send sender receiver msg"
    and "\<forall>sender receiver msg. a \<noteq> Receive sender receiver msg"
    and "s = (tn app1 kme1 app2 kme2 bridge1 bridge2, qkd, msgs)"
    and "t = (tn app1 kme1 app2 kme2 bridge1' bridge2', qkd, msgs)"
    and "i \<in> c_nodes"
    and "b \<in> c_bridgeIDs i"
    and bridge_trans: "(snd (snd (fst s i)) b, a, snd (snd (fst t i)) b) \<in> trans_of (SingleHop.bridge.ioa b i)"
    and "(i = Node1 \<longrightarrow> bridge2 = bridge2') \<and> (i = Node2 \<longrightarrow> bridge1 = bridge1')"
  shows "(s,a,t) \<in> trans_of SingleHop.System.ioa"
proof -
  have a_act_bridge: "a \<in> act (SingleHop.bridge.ioa b i)"
    using bridge_trans SingleHop.bridge.is_ioa[of b i] unfolding Automata.IOA_def is_trans_of_def by fastforce
  have a_in_tn: "a \<in> act (SingleHop.trusted_node.ioa i)"
    by (intro par_actR set_ioa_actI[of b] assms(6) a_act_bridge)
  have a_in_tns: "a \<in> act SingleHop.trusted_nodes.ioa"
    unfolding actions_of_set_ioa using assms(5) a_in_tn by fast
  show ?thesis
  proof (rule trans_par_inductFst)
    show "a \<in> act SingleHop.trusted_nodes.ioa"
      by (rule a_in_tns)
    show "fst s \<midarrow>a\<midarrow>SingleHop.trusted_nodes.ioa\<rightarrow> fst t"
    proof (rule trans_set_ioa_induct[of i])
      show "i \<in> c_nodes" 
        by (rule assms(5))
      show "a \<in> act (SingleHop.trusted_node.ioa i)" 
        by (rule a_in_tn)
      show "fst s i \<midarrow>a\<midarrow>SingleHop.trusted_node.ioa i\<rightarrow> fst t i"
      proof (rule trans_par_inductSnd)
        show "a \<notin> act (SingleHop.app.ioa i)"
          using a_act_bridge assms(5,6) app_kme_bridges_act_distinct
          unfolding actions_of_par actions_of_set_ioa by fast
        show "a \<in> act (SingleHop.kme_bridges.ioa i)"
          using a_act_bridge assms(6)
          unfolding actions_of_par actions_of_set_ioa by blast
        show "snd (fst s i) \<midarrow>a\<midarrow>SingleHop.kme_bridges.ioa i\<rightarrow> snd (fst t i)" 
        proof (rule trans_par_inductSnd)
          show "a \<notin> act (SingleHop.kme.ioa i)"
            using a_act_bridge assms(5,6) kme_bridges_act_distinct
            unfolding actions_of_set_ioa by fast
          show "a \<in> act (SingleHop.bridges.ioa i)"
            unfolding actions_of_set_ioa 
            using a_act_bridge assms(6) by fast
          show "snd (snd (fst s i)) \<midarrow>a\<midarrow>SingleHop.bridges.ioa i\<rightarrow> snd (snd (fst t i))"
          proof (rule trans_set_ioa_induct)
            show "b \<in> c_bridgeIDs i"
              using assms(6) .
            show "a \<in> act (SingleHop.bridge.ioa b i)"
              using a_act_bridge .
            show "snd (snd (fst s i)) b \<midarrow>a\<midarrow>SingleHop.bridge.ioa b i\<rightarrow> snd (snd (fst t i)) b"
              using assms(7) .
            show "\<forall>ia\<in>c_bridgeIDs i. ia \<noteq> b \<longrightarrow> a \<notin> act (SingleHop.bridge.ioa ia i)"
              using bridge_act_distinct a_act_bridge assms(5,6) by blast
            show "snd (snd (fst t i)) = (snd (snd (fst s i)))(b := snd (snd (fst t i)) b)"
              apply(simp only: assms tn_def bridge_def; simp)
              using assms(6) c_bridgeIDs_def by auto
          qed
          show "fst (snd (fst s i)) = fst (snd (fst t i))"
            by(simp only: assms tn_def; simp)
        qed
        show "fst (fst s i) = fst (fst t i)"
          using a_act_bridge assms
          unfolding actions_of_par actions_of_set_ioa actions_def asig_projections asig_of_def 
                    c_isMaster_def c_appID_def c_bridgeIDs_def c_kmeID_def c_nodes_def tn_def bridge_def
          by (auto split: if_splits)
      qed
      show "\<forall>ia\<in>c_nodes. ia \<noteq> i \<longrightarrow> a \<notin> act (SingleHop.trusted_node.ioa ia)"
        using trusted_node_act_distinct a_in_tn assms(5) by blast 
      show "fst t = (fst s)(i := fst t i)"
        using assms by (auto simp: tn_def c_nodes_def)
    qed
    show "a \<notin> act SingleHop.qkd_layer_network.ioa"
    proof (rule no_par_act)
      show "a \<notin> act SingleHop.qkd_layer.ioa"
        using a_in_tns tns_qkd_layer_act_distinct by blast
      show "a \<notin> act SingleHop.network.ioa"
        using a_in_tns tns_network_acts_inter assms(1,2) by blast
    qed
    show "snd s = snd t"
      using assms(3,4) by simp
  qed
qed

lemma trans_in_app_netw:
  assumes "\<exists>sender msg rcpt. a = Receive sender rcpt msg \<or> a = Send sender rcpt msg"
    and "s = (tn app1 kme1 app2 kme2 bridge1 bridge2, qkd, msgs)"
    and "t = (tn app1' kme1 app2' kme2 bridge1 bridge2, qkd, msgs')"
    and "i \<in> c_nodes"
    and app_trans: "(fst (fst s i), a, fst (fst t i)) \<in> trans_of (SingleHop.app.ioa i)"
    and netw_trans: "(network s, a, network t) \<in> trans_of (SingleHop.network.ioa)"
    and "(i = Node1 \<longrightarrow> app2 = app2') \<and> (i = Node2 \<longrightarrow> app1 = app1')"
  shows "(s,a,t) \<in> trans_of SingleHop.System.ioa"
proof -
  have a_act_app: "a \<in> act (SingleHop.app.ioa i)"
    using app_trans SingleHop.app.is_ioa[of i] unfolding Automata.IOA_def is_trans_of_def by fastforce
  have a_in_tn: "a \<in> act (SingleHop.trusted_node.ioa i)"
    by (intro par_actL a_act_app)
  have a_in_tns: "a \<in> act SingleHop.trusted_nodes.ioa"
    unfolding actions_of_set_ioa using assms(4) a_in_tn by fast
  show ?thesis
  proof (rule trans_par_inductFst_Gen)
    show "a \<in> act SingleHop.trusted_nodes.ioa" 
      by (rule a_in_tns)
    show "fst s \<midarrow>a\<midarrow>SingleHop.trusted_nodes.ioa\<rightarrow> fst t"
    proof (rule trans_set_ioa_induct[of i])
      show "i \<in> c_nodes" 
        by (rule assms(4))
      show "a \<in> act (SingleHop.trusted_node.ioa i)" 
        by (rule a_in_tn)
      show "fst s i \<midarrow>a\<midarrow>SingleHop.trusted_node.ioa i\<rightarrow> fst t i"
      proof (rule trans_par_inductFst)
        show "a \<in> act (SingleHop.app.ioa i)" 
          by (rule a_act_app)
        show "fst (fst s i) \<midarrow>a\<midarrow>SingleHop.app.ioa i\<rightarrow> fst (fst t i)" 
          by (rule app_trans)
        show "a \<notin> act (SingleHop.kme_bridges.ioa i)"
          using a_act_app assms(4) app_kme_bridges_act_distinct by fast
        show "snd (fst s i) = snd (fst t i)"
          using a_act_app assms
          unfolding actions_of_par actions_of_set_ioa actions_def asig_projections asig_of_def 
                    c_isMaster_def c_appID_def c_bridgeIDs_def c_kmeID_def c_nodes_def tn_def bridge_def
          by (auto split: if_splits)
      qed
      show "\<forall>ia\<in>c_nodes. ia \<noteq> i \<longrightarrow> a \<notin> act (SingleHop.trusted_node.ioa ia)"
        using trusted_node_act_distinct a_in_tn assms(4) by blast 
      show "fst t = (fst s)(i := fst t i)"
        using assms by (auto simp: tn_def c_nodes_def)
    qed
    show "a \<in> act SingleHop.qkd_layer_network.ioa \<longrightarrow> snd s \<midarrow>a\<midarrow>SingleHop.qkd_layer_network.ioa\<rightarrow> snd t"
    proof
      assume "a \<in> act SingleHop.qkd_layer_network.ioa"
      show "snd s \<midarrow>a\<midarrow>SingleHop.qkd_layer_network.ioa\<rightarrow> snd t"
      proof (rule trans_par_inductSnd)
        show "a \<notin> act SingleHop.qkd_layer.ioa"
          using tns_qkd_layer_act_distinct a_in_tns by blast
        show "a \<in> act SingleHop.network.ioa"
          using assms(1)
          unfolding actions_def asig_projections asig_of_def apply simp
          unfolding c_appID_def c_kmeID_def c_bridgeIDs_def c_nodes_def c_qkdID_def apply simp
          using concrete_node.exhaust concrete_proc.exhaust apply auto
          by (metis (full_types))+
        show "network s \<midarrow>a\<midarrow>SingleHop.network.ioa\<rightarrow> network t"
          using assms(6) .
        show "qkd_layer s = qkd_layer t"
          using assms(2,3) by simp
      qed
    qed
    show "a \<notin> act SingleHop.qkd_layer_network.ioa \<longrightarrow> snd s = snd t"
      unfolding actions_of_par
      using assms(2,3,6) SingleHop.network.is_trans_of
      unfolding is_trans_of_def by auto
  qed
qed

lemma trans_in_kme_netw:
  assumes "\<exists>sender msg rcpt. a = Receive sender rcpt msg \<or> a = Send sender rcpt msg"
    and "s = (tn app1 kme1 app2 kme2 bridge1 bridge2, qkd, msgs)"
    and "t = (tn app1 kme1' app2 kme2' bridge1 bridge2, qkd, msgs')"
    and "i \<in> c_nodes"
    and kme_trans: "(fst (snd (fst s i)), a, fst (snd (fst t i))) \<in> trans_of (SingleHop.kme.ioa i)"
    and netw_trans: "(network s, a, network t) \<in> trans_of (SingleHop.network.ioa)"
    and "(i = Node1 \<longrightarrow> kme2 = kme2') \<and> (i = Node2 \<longrightarrow> kme1 = kme1')"
  shows "(s,a,t) \<in> trans_of SingleHop.System.ioa"
proof -
  have a_act_kme: "a \<in> act (SingleHop.kme.ioa i)"
    using kme_trans SingleHop.kme.is_ioa[of i] unfolding Automata.IOA_def is_trans_of_def by fastforce
  have a_in_tn: "a \<in> act (SingleHop.trusted_node.ioa i)"
    by (intro par_actR par_actL a_act_kme)
  have a_in_tns: "a \<in> act SingleHop.trusted_nodes.ioa"
    unfolding actions_of_set_ioa using assms(4) a_in_tn by fast
  show ?thesis
  proof (rule trans_par_inductFst_Gen)
    show "a \<in> act SingleHop.trusted_nodes.ioa" 
      by (rule a_in_tns)
    show "fst s \<midarrow>a\<midarrow>SingleHop.trusted_nodes.ioa\<rightarrow> fst t"
    proof (rule trans_set_ioa_induct[of i])
      show "i \<in> c_nodes" 
        by (rule assms(4))
      show "a \<in> act (SingleHop.trusted_node.ioa i)" 
        by (rule a_in_tn)
      show "fst s i \<midarrow>a\<midarrow>SingleHop.trusted_node.ioa i\<rightarrow> fst t i"
      proof (rule trans_par_inductSnd)
        show "a \<notin> act (SingleHop.app.ioa i)"
          using a_act_kme assms(4) app_kme_bridges_act_distinct
          unfolding actions_of_par by blast
        show "a \<in> act (SingleHop.kme_bridges.ioa i)"
          using a_act_kme
          unfolding actions_of_par by blast
        show "snd (fst s i) \<midarrow>a\<midarrow>SingleHop.kme_bridges.ioa i\<rightarrow> snd (fst t i)" 
        proof (rule trans_par_inductFst)
          show "a \<in> act (SingleHop.kme.ioa i)"
            using a_act_kme .
          show "fst (snd (fst s i)) \<midarrow>a\<midarrow>SingleHop.kme.ioa i\<rightarrow> fst (snd (fst t i))"
            using assms(5) .
          show "a \<notin> act (SingleHop.bridges.ioa i)"
            using kme_bridges_act_distinct a_act_kme assms(4) by fast
          show "snd (snd (fst s i)) = snd (snd (fst t i))"
            by(simp only: assms tn_def; simp)
        qed
        show "fst (fst s i) = fst (fst t i)"
          using a_act_kme assms
          unfolding actions_of_par actions_of_set_ioa actions_def asig_projections asig_of_def 
                    c_isMaster_def c_appID_def c_bridgeIDs_def c_kmeID_def c_nodes_def tn_def bridge_def
          by (auto split: if_splits)
      qed
      show "\<forall>ia\<in>c_nodes. ia \<noteq> i \<longrightarrow> a \<notin> act (SingleHop.trusted_node.ioa ia)"
        using trusted_node_act_distinct a_in_tn assms(4) by blast 
      show "fst t = (fst s)(i := fst t i)"
        using assms by (auto simp: tn_def c_nodes_def)
    qed
    show "a \<in> act SingleHop.qkd_layer_network.ioa \<longrightarrow> snd s \<midarrow>a\<midarrow>SingleHop.qkd_layer_network.ioa\<rightarrow> snd t"
    proof
      assume "a \<in> act SingleHop.qkd_layer_network.ioa"
      show "snd s \<midarrow>a\<midarrow>SingleHop.qkd_layer_network.ioa\<rightarrow> snd t"
      proof (rule trans_par_inductSnd)
        show "a \<notin> act SingleHop.qkd_layer.ioa"
          using tns_qkd_layer_act_distinct a_in_tns by blast
        show "a \<in> act SingleHop.network.ioa"
          using assms(1)
          unfolding actions_def asig_projections asig_of_def apply simp
          unfolding c_appID_def c_kmeID_def c_bridgeIDs_def c_nodes_def c_qkdID_def apply simp
          using concrete_node.exhaust concrete_proc.exhaust apply auto
          by (metis (full_types))+
        show "network s \<midarrow>a\<midarrow>SingleHop.network.ioa\<rightarrow> network t"
          using assms(6) .
        show "qkd_layer s = qkd_layer t"
          using assms(2,3) by simp
      qed
    qed
    show "a \<notin> act SingleHop.qkd_layer_network.ioa \<longrightarrow> snd s = snd t"
      unfolding actions_of_par
      using assms(2,3,6) SingleHop.network.is_trans_of
      unfolding is_trans_of_def by auto
  qed
qed

lemma trans_in_bridge_netw:
  assumes "\<exists>sender msg rcpt. a = Receive sender rcpt msg \<or> a = Send sender rcpt msg"
    and "s = (tn app1 kme1 app2 kme2 bridge1 bridge2, qkd, msgs)"
    and "t = (tn app1 kme1 app2 kme2 bridge1' bridge2', qkd, msgs')"
    and "i \<in> c_nodes"
    and "b \<in> c_bridgeIDs i"
    and bridge_trans: "(snd (snd (fst s i)) b, a, snd (snd (fst t i)) b) \<in> trans_of (SingleHop.bridge.ioa b i)"
    and netw_trans: "(network s, a, network t) \<in> trans_of (SingleHop.network.ioa)"
    and "(i = Node1 \<longrightarrow> bridge2 = bridge2') \<and> (i = Node2 \<longrightarrow> bridge1 = bridge1')"
  shows "(s,a,t) \<in> trans_of SingleHop.System.ioa"
proof -
  have a_act_bridge: "a \<in> act (SingleHop.bridge.ioa b i)"
    using bridge_trans SingleHop.bridge.is_ioa[of b i] unfolding Automata.IOA_def is_trans_of_def by fastforce
  have a_in_tn: "a \<in> act (SingleHop.trusted_node.ioa i)"
    by (intro par_actR set_ioa_actI[of b] assms(5) a_act_bridge)
  have a_in_tns: "a \<in> act SingleHop.trusted_nodes.ioa"
    unfolding actions_of_set_ioa using assms(4) a_in_tn by fast
  show ?thesis
  proof (rule trans_par_inductFst_Gen)
    show "a \<in> act SingleHop.trusted_nodes.ioa"
      by (rule a_in_tns)
    show "fst s \<midarrow>a\<midarrow>SingleHop.trusted_nodes.ioa\<rightarrow> fst t"
    proof (rule trans_set_ioa_induct[of i])
      show "i \<in> c_nodes" 
        by (rule assms(4))
      show "a \<in> act (SingleHop.trusted_node.ioa i)" 
        by (rule a_in_tn)
      show "fst s i \<midarrow>a\<midarrow>SingleHop.trusted_node.ioa i\<rightarrow> fst t i"
      proof (rule trans_par_inductSnd)
        show "a \<notin> act (SingleHop.app.ioa i)"
          using a_act_bridge assms(4,5) app_kme_bridges_act_distinct
          unfolding actions_of_par actions_of_set_ioa by fast
        show "a \<in> act (SingleHop.kme_bridges.ioa i)"
          using a_act_bridge assms(5)
          unfolding actions_of_par actions_of_set_ioa by blast
        show "snd (fst s i) \<midarrow>a\<midarrow>SingleHop.kme_bridges.ioa i\<rightarrow> snd (fst t i)" 
        proof (rule trans_par_inductSnd)
          show "a \<notin> act (SingleHop.kme.ioa i)"
            using a_act_bridge assms(4,5) kme_bridges_act_distinct
            unfolding actions_of_set_ioa by fast
          show "a \<in> act (SingleHop.bridges.ioa i)"
            unfolding actions_of_set_ioa 
            using a_act_bridge assms(5) by fast
          show "snd (snd (fst s i)) \<midarrow>a\<midarrow>SingleHop.bridges.ioa i\<rightarrow> snd (snd (fst t i))"
          proof (rule trans_set_ioa_induct)
            show "b \<in> c_bridgeIDs i"
              using assms(5) .
            show "a \<in> act (SingleHop.bridge.ioa b i)"
              using a_act_bridge .
            show "snd (snd (fst s i)) b \<midarrow>a\<midarrow>SingleHop.bridge.ioa b i\<rightarrow> snd (snd (fst t i)) b"
              using assms(6) .
            show "\<forall>ia\<in>c_bridgeIDs i. ia \<noteq> b \<longrightarrow> a \<notin> act (SingleHop.bridge.ioa ia i)"
              using bridge_act_distinct a_act_bridge assms(4,5) by blast
            show "snd (snd (fst t i)) = (snd (snd (fst s i)))(b := snd (snd (fst t i)) b)"
              apply(simp only: assms tn_def bridge_def; simp)
              using assms(5) c_bridgeIDs_def by auto
          qed
          show "fst (snd (fst s i)) = fst (snd (fst t i))"
            by(simp only: assms tn_def; simp)
        qed
        show "fst (fst s i) = fst (fst t i)"
          using a_act_bridge assms
          unfolding actions_of_par actions_of_set_ioa actions_def asig_projections asig_of_def 
                    c_isMaster_def c_appID_def c_bridgeIDs_def c_kmeID_def c_nodes_def tn_def bridge_def
          by (auto split: if_splits)
      qed
      show "\<forall>ia\<in>c_nodes. ia \<noteq> i \<longrightarrow> a \<notin> act (SingleHop.trusted_node.ioa ia)"
        using trusted_node_act_distinct a_in_tn assms(4) by blast 
      show "fst t = (fst s)(i := fst t i)"
        using assms by (auto simp: tn_def c_nodes_def)
    qed
    show "a \<in> act SingleHop.qkd_layer_network.ioa \<longrightarrow> snd s \<midarrow>a\<midarrow>SingleHop.qkd_layer_network.ioa\<rightarrow> snd t"
    proof
      assume "a \<in> act SingleHop.qkd_layer_network.ioa"
      show "snd s \<midarrow>a\<midarrow>SingleHop.qkd_layer_network.ioa\<rightarrow> snd t"
      proof (rule trans_par_inductSnd)
        show "a \<notin> act SingleHop.qkd_layer.ioa"
          using tns_qkd_layer_act_distinct a_in_tns by blast
        show "a \<in> act SingleHop.network.ioa"
          using assms(1)
          unfolding actions_def asig_projections asig_of_def apply simp
          unfolding c_appID_def c_kmeID_def c_bridgeIDs_def c_nodes_def c_qkdID_def apply simp
          using concrete_node.exhaust concrete_proc.exhaust apply auto
          by (metis (full_types))+
        show "network s \<midarrow>a\<midarrow>SingleHop.network.ioa\<rightarrow> network t"
          using assms(7) .
        show "qkd_layer s = qkd_layer t"
          using assms(2,3) by simp
      qed
    qed
    show "a \<notin> act SingleHop.qkd_layer_network.ioa \<longrightarrow> snd s = snd t"
      unfolding actions_of_par
      using assms(7) SingleHop.network.is_trans_of
      unfolding is_trans_of_def by auto
  qed
qed

lemma trans_in_qkd_netw:
  assumes "\<exists>sender msg rcpt. a = Receive sender rcpt msg \<or> a = Send sender rcpt msg"
    and "s = (tn app1 kme1 app2 kme2 bridge1 bridge2, qkd, msgs)"
    and "t = (tn app1 kme1 app2 kme2 bridge1 bridge2, qkd', msgs')"
    and qkd_trans: "(fst (snd s), a, fst (snd t)) \<in> trans_of (SingleHop.qkd_layer.ioa)"
    and netw_trans: "(network s, a, network t) \<in> trans_of (SingleHop.network.ioa)"
  shows "(s,a,t) \<in> trans_of SingleHop.System.ioa"
proof -
  have a_act_qkd: "a \<in> act (SingleHop.qkd_layer.ioa)"
    using qkd_trans SingleHop.qkd_layer.is_trans_of unfolding is_trans_of_def by auto
  have a_act_network: "a \<in> act (SingleHop.network.ioa)"
    using netw_trans SingleHop.network.is_trans_of unfolding is_trans_of_def by auto
  have a_act_qkd_network: "a \<in> act (SingleHop.qkd_layer_network.ioa)"
    unfolding actions_of_par using a_act_qkd by blast
  show ?thesis
  proof (rule trans_par_inductSnd_Gen)
    show "a \<notin> act SingleHop.trusted_nodes.ioa \<longrightarrow> fst s = fst t"
      using tns_qkd_layer_act_distinct a_act_qkd assms(2,3) by auto
    show "a \<in> act SingleHop.trusted_nodes.ioa \<longrightarrow> fst s \<midarrow>a\<midarrow>SingleHop.trusted_nodes.ioa\<rightarrow> fst t"
      using tns_qkd_layer_act_distinct a_act_qkd by blast
    show "a \<in> act SingleHop.qkd_layer_network.ioa"
      using a_act_qkd_network .
    show "snd s \<midarrow>a\<midarrow>SingleHop.qkd_layer_network.ioa\<rightarrow> snd t"
      apply (simp only: assms tn_def snd_conv)
      unfolding trans_of_par
      using assms(2-5) a_act_qkd a_act_network
      unfolding tn_def by (auto simp add: Let_def)
  qed
qed

end