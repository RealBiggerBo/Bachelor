theory QKD_Interpretation_Single_Hop_Trans_Helpers
  imports QKD_Interpretation_Single_Hop
begin

lemma trans_in_app_no_netw:
  assumes "\<forall>sender receiver msg. a \<noteq> Send sender receiver msg"
    and "\<forall>sender receiver msg. a \<noteq> Receive sender receiver msg"
    and "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, msgs)"
    and "t = (apps app1' app2', kmes kme1 kme2, bridges bridge1 bridge2, qkd, msgs)"
    and "i \<in> c_nodes"
    and app_trans: "(app s i, a, app t i) \<in> trans_of (SingleHop.app.ioa i)"
    and "(i = Node1 \<longrightarrow> app2 = app2') \<and> (i = Node2 \<longrightarrow> app1 = app1')"
  shows "(s,a,t) \<in> trans_of SingleHop.System.ioa"
proof -
  have a_act_app: "a \<in> act (SingleHop.app.ioa i)"
    using app_trans SingleHop.app.is_ioa[of i] unfolding Automata.IOA_def is_trans_of_def by fastforce
  have a_in_apps: "a \<in> act SingleHop.apps.ioa"
    unfolding actions_of_set_ioa using a_act_app assms(5) by blast
  show ?thesis
  proof (rule trans_par_inductFst)
    show "a \<in> act SingleHop.apps.ioa" 
      by (rule a_in_apps)
    show "app s \<midarrow>a\<midarrow>SingleHop.apps.ioa\<rightarrow> app t"
    proof (rule trans_set_ioa_induct[of i])
      show "i \<in> c_nodes" 
        by (rule assms(5))
      show "a \<in> act (SingleHop.app.ioa i)" 
        by (rule a_act_app)
      show "fst s i \<midarrow>a\<midarrow>SingleHop.app.ioa i\<rightarrow> fst t i"
        using assms(6) .
      show "\<forall>ia\<in>c_nodes. ia \<noteq> i \<longrightarrow> a \<notin> act (SingleHop.app.ioa ia)"
        using SingleHop.actsDisj_app_app a_act_app assms(5) by blast
      show "app t = (app s)(i := app t i)"
        using assms by (auto simp: apps_def c_nodes_def)
    qed
    show "a \<notin> act SingleHop.kmes_bridges_qkd_layer_network.ioa"
      apply(rule no_par_act)
      unfolding actions_of_set_ioa
      using a_act_app assms(5) SingleHop.actsDisj_app_kme apply fast
      apply(rule no_par_act)
      unfolding actions_of_set_ioa
      using a_act_app assms(5) SingleHop.actsDisj_app_bridge apply fast
      apply(rule no_par_act)
      unfolding actions_of_set_ioa
      using a_act_app assms(5) SingleHop.actsDisj_app_qkd apply fast
      using assms(1,2) unfolding actions_def asig_projections asig_of_def by simp
    show "snd s = snd t"
      by(subst assms(3,4); auto)+
  qed
qed

lemma trans_in_kme_no_netw:
  assumes "\<forall>sender receiver msg. a \<noteq> Send sender receiver msg"
    and "\<forall>sender receiver msg. a \<noteq> Receive sender receiver msg"
    and "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, msgs)"
    and "t = (apps app1 app2, kmes kme1' kme2', bridges bridge1 bridge2, qkd, msgs)"
    and "i \<in> c_nodes"
    and kme_trans: "(kme s i, a, kme t i) \<in> trans_of (SingleHop.kme.ioa i)"
    and "(i = Node1 \<longrightarrow> kme2 = kme2') \<and> (i = Node2 \<longrightarrow> kme1 = kme1')"
  shows "(s,a,t) \<in> trans_of SingleHop.System.ioa"
proof -
  have a_act_kme: "a \<in> act (SingleHop.kme.ioa i)"
    using kme_trans SingleHop.kme.is_ioa[of i] unfolding Automata.IOA_def is_trans_of_def by fastforce
  have a_in_kmes: "a \<in> act SingleHop.kmes.ioa"
    unfolding actions_of_set_ioa using assms(5) a_act_kme by blast
  show ?thesis
  proof (rule trans_par_inductSnd)
    show "a \<notin> act SingleHop.apps.ioa" 
      unfolding actions_of_set_ioa
      using a_act_kme SingleHop.actsDisj_app_kme assms(5) by fast
    show "a \<in> act SingleHop.kmes_bridges_qkd_layer_network.ioa"
      apply(rule par_actL)
      using a_in_kmes .
    show "snd s \<midarrow>a\<midarrow>SingleHop.kmes_bridges_qkd_layer_network.ioa\<rightarrow> snd t"
    proof (rule trans_par_inductFst)
      show "a \<in> act SingleHop.kmes.ioa"
        using a_in_kmes .
      show "kme s \<midarrow>a\<midarrow>SingleHop.kmes.ioa\<rightarrow> kme t"
      proof(rule trans_set_ioa_induct)
        show "i \<in> c_nodes"
          using assms(5) .
        show "a \<in> act (SingleHop.kme.ioa i)"
          using a_act_kme .
        show "kme s i \<midarrow>a\<midarrow>SingleHop.kme.ioa i\<rightarrow> kme t i"
          using assms(6) .
        show "\<forall>ia\<in>c_nodes. ia \<noteq> i \<longrightarrow> a \<notin> act (SingleHop.kme.ioa ia)"
          using SingleHop.actsDisj_kme_kme assms(5) a_act_kme by blast
        show "kme t = (kme s)(i := kme t i)"
          apply(subst assms(3,4); simp add: kmes_def assms(7))+
          using assms(5) unfolding c_nodes_def by auto
      qed
      show "a \<notin> act SingleHop.bridges_qkd_layer_network.ioa"
        apply (rule no_par_act)
        unfolding actions_of_set_ioa
        using a_act_kme SingleHop.actsDisj_kme_bridge assms(5) apply fast
        apply (rule no_par_act)
        using a_act_kme SingleHop.actsDisj_kme_qkd assms(5) apply fast
        using assms(1,2) unfolding actions_def asig_projections asig_of_def by simp
      show "snd (snd s) = snd (snd t)"
        by(subst assms(3,4); simp)+
    qed
    show "app s = app t"
      by(subst assms(3,4); auto)+
  qed
qed

lemma trans_in_bridge_no_netw:
  assumes "\<forall>sender receiver msg. a \<noteq> Send sender receiver msg"
    and "\<forall>sender receiver msg. a \<noteq> Receive sender receiver msg"
    and "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, msgs)"
    and "t = (apps app1 app2, kmes kme1 kme2, bridges bridge1' bridge2', qkd, msgs)"
    and "i \<in> c_nodes"
    and "b \<in> c_bridgeIDs i"
    and bridge_trans: "(bridge s i b, a, bridge t i b) \<in> trans_of (SingleHop.bridge.ioa b i)"
    and "(i = Node1 \<longrightarrow> bridge2 = bridge2') \<and> (i = Node2 \<longrightarrow> bridge1 = bridge1')"
  shows "(s,a,t) \<in> trans_of SingleHop.System.ioa"
proof -
  have a_act_bridge: "a \<in> act (SingleHop.bridge.ioa b i)"
    using bridge_trans SingleHop.bridge.is_ioa[of b i] unfolding Automata.IOA_def is_trans_of_def by fastforce
  have a_in_bridges: "a \<in> act SingleHop.bridges.ioa"
    unfolding actions_of_set_ioa using assms(5,6) a_act_bridge by fast
  show ?thesis
  proof (rule trans_par_inductSnd)
    show "a \<notin> act SingleHop.apps.ioa"
      unfolding actions_of_set_ioa
      using a_act_bridge SingleHop.actsDisj_app_bridge assms(5,6) by fast
    show "a \<in> act SingleHop.kmes_bridges_qkd_layer_network.ioa"
      apply (rule par_actR)
      apply (rule par_actL)
      using a_in_bridges .
    show "snd s \<midarrow>a\<midarrow>SingleHop.kmes_bridges_qkd_layer_network.ioa\<rightarrow> snd t"
    proof (rule trans_par_inductSnd)
      show "a \<notin> act SingleHop.kmes.ioa"
        unfolding actions_of_set_ioa
        using a_act_bridge SingleHop.actsDisj_kme_bridge assms(5,6) by fast
      show "a \<in> act SingleHop.bridges_qkd_layer_network.ioa"
        apply (rule par_actL)
        using a_in_bridges .
      show "snd (snd s) \<midarrow>a\<midarrow>SingleHop.bridges_qkd_layer_network.ioa\<rightarrow> snd (snd t)"
      proof (rule trans_par_inductFst)
        show "a \<in> act SingleHop.bridges.ioa"
          using a_in_bridges .
        show "fst (snd (snd s)) \<midarrow>a\<midarrow>SingleHop.bridges.ioa\<rightarrow> fst (snd (snd t))"
        proof (rule trans_set_ioa_induct)
          show "(i,b) \<in> Sigma c_nodes c_bridgeIDs"
            using assms(5,6) by simp
          show "a \<in> act (case (i, b) of (nodeID, bridgeID) \<Rightarrow> SingleHop.bridge.ioa bridgeID nodeID)"
            using a_act_bridge by fastforce
          show "bridge s i b \<midarrow>a\<midarrow>(case (i, b) of (nodeID, bridgeID) \<Rightarrow> SingleHop.bridge.ioa bridgeID nodeID)\<rightarrow> bridge t i b"
            using assms(7) by force
          show "\<forall>ia\<in>Sigma c_nodes c_bridgeIDs.
                   ia \<noteq> (i, b) \<longrightarrow> a \<notin> act (case ia of (nodeID, bridgeID) \<Rightarrow> SingleHop.bridge.ioa bridgeID nodeID)"
          proof (rule; rule)
            fix ia
            assume ia_sigma: "ia \<in> Sigma c_nodes c_bridgeIDs"
            assume ia_neq: "ia \<noteq> (i, b)"
            obtain nodeID bridgeID where split:"ia = (nodeID, bridgeID)"
              by fastforce
            then have "bridgeID \<noteq> b"
              using SingleHop.disjoint_node_bridges ia_sigma assms(5,6) ia_neq apply auto
              unfolding disjnt_def by blast
            moreover have "nodeID \<in> c_nodes"
              using ia_sigma split Sigma_def by blast
            moreover have "bridgeID \<in> c_bridgeIDs nodeID"
              using ia_sigma split Sigma_def by force
            ultimately have "a \<notin> act (SingleHop.bridge.ioa bridgeID nodeID)"
              using a_act_bridge assms(5,6) SingleHop.actsDisj_bridge_bridge[of i nodeID b bridgeID] by blast
            then show "a \<notin> act (case ia of (nodeID, bridgeID) \<Rightarrow> SingleHop.bridge.ioa bridgeID nodeID)"
              using split by fast
          qed
          show "fst (snd (snd t)) = (fst (snd (snd s)))((i, b) := bridge t i b)"
            apply(subst assms(3,4); simp add: bridges_def assms(8))+
            using assms(5,6) unfolding c_nodes_def c_bridgeIDs_def by auto
        qed
        show "a \<notin> act SingleHop.qkd_layer_network.ioa"
          apply (rule no_par_act)
          unfolding actions_of_set_ioa
          using a_act_bridge SingleHop.actsDisj_bridge_qkd assms(5,6) apply fast
        proof
          assume "a \<in> act SingleHop.network.ioa"
          then have "a \<in> act (SingleHop.bridge.ioa b i) \<inter> act SingleHop.network.ioa"
            using a_act_bridge by simp
          then have "\<And>all. all = c_appID ` c_nodes \<union> c_kmeID ` c_nodes \<union> \<Union> (c_bridgeIDs ` c_nodes) \<union> c_qkdID ` \<Union> (c_bridgeIDs ` c_nodes) \<Longrightarrow>
                          a \<in> {Send b rcpt msg |rcpt msg. rcpt \<in> all} \<union> 
                              {Receive sender b msg |sender msg. sender \<in> all}"
            using assms(5,6) SingleHop.acts_bridge_netw
            using assms(1,2) unfolding actions_def asig_projections asig_of_def by simp
          then show False
            using assms(1,2) by fastforce
        qed
        show "snd (snd (snd s)) = snd (snd (snd t))"
          by (subst assms(3,4); simp)+
      qed
      show "fst (snd s) = fst (snd t)"
        by (subst assms(3,4); auto)+
    qed
    show "app s = app t"
      by (subst assms(3,4); auto)+
  qed
qed

lemma trans_in_app_netw:
  assumes "\<exists>sender msg rcpt. a = Receive sender rcpt msg \<or> a = Send sender rcpt msg"
    and "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, msgs)"
    and "t = (apps app1' app2', kmes kme1 kme2, bridges bridge1 bridge2, qkd, msgs')"
    and "i \<in> c_nodes"
    and app_trans: "(app s i, a, app t i) \<in> trans_of (SingleHop.app.ioa i)"
    and netw_trans: "(network s, a, network t) \<in> trans_of (SingleHop.network.ioa)"
    and "(i = Node1 \<longrightarrow> app2 = app2') \<and> (i = Node2 \<longrightarrow> app1 = app1')"
  shows "(s,a,t) \<in> trans_of SingleHop.System.ioa"
proof -
  have a_act_app: "a \<in> act (SingleHop.app.ioa i)"
    using app_trans SingleHop.app.is_ioa[of i] unfolding Automata.IOA_def is_trans_of_def by fastforce
  have a_in_apps: "a \<in> act SingleHop.apps.ioa"
    unfolding actions_of_set_ioa using assms(4) a_act_app by fast
  have a_act_netw: "a \<in> act SingleHop.network.ioa"
    using netw_trans SingleHop.network.is_trans_of unfolding is_trans_of_def by auto
  show ?thesis
  proof (rule trans_par_inductFst_Gen)
    show "a \<in> act SingleHop.apps.ioa"
      using a_in_apps .
    show "app s \<midarrow>a\<midarrow>SingleHop.apps.ioa\<rightarrow> app t"
    proof (rule trans_set_ioa_induct[of i])
      show "i \<in> c_nodes"
        by (rule assms(4))
      show "a \<in> act (SingleHop.app.ioa i)"
        by (rule a_act_app)
      show "app s i \<midarrow>a\<midarrow>SingleHop.app.ioa i\<rightarrow> app t i"
        using assms(5) .
      show "\<forall>ia\<in>c_nodes. ia \<noteq> i \<longrightarrow> a \<notin> act (SingleHop.app.ioa ia)"
        using SingleHop.actsDisj_app_app assms(4) a_act_app by blast
      show "app t = (app s)(i := app t i)"
        apply(subst assms(2,3); simp add: apps_def assms(7))+
        using assms(4) unfolding c_nodes_def by fastforce
    qed
    show "a \<in> act SingleHop.kmes_bridges_qkd_layer_network.ioa \<longrightarrow>
           snd s \<midarrow>a\<midarrow>SingleHop.kmes_bridges_qkd_layer_network.ioa\<rightarrow> snd t"
    proof (rule; rule trans_par_inductSnd)
      show "a \<notin> act SingleHop.kmes.ioa"
        unfolding actions_of_set_ioa
        using a_act_app SingleHop.actsDisj_app_kme assms(4) by fast
      show "a \<in> act SingleHop.bridges_qkd_layer_network.ioa"
        apply (rule par_actR; rule par_actR)
        using a_act_netw .
      show "snd (snd s) \<midarrow>a\<midarrow>SingleHop.bridges_qkd_layer_network.ioa\<rightarrow> snd (snd t)"
      proof (rule trans_par_inductSnd)
        show "a \<notin> act SingleHop.bridges.ioa"
          unfolding actions_of_set_ioa
          using a_act_app SingleHop.actsDisj_app_bridge assms(4) by fast
        show "a \<in> act SingleHop.qkd_layer_network.ioa"
          apply (rule par_actR)
          using a_act_netw .
        show "snd (snd (snd s)) \<midarrow>a\<midarrow>SingleHop.qkd_layer_network.ioa\<rightarrow> snd (snd (snd t))"
        proof (rule trans_par_inductSnd)
          show "a \<notin> act SingleHop.qkd_layer.ioa"
            using a_act_app SingleHop.actsDisj_app_qkd assms(4) by fast
          show "a \<in> act SingleHop.network.ioa"
            using a_act_netw .
          show "network s \<midarrow>a\<midarrow>SingleHop.network.ioa\<rightarrow> network t"
            using assms(6) .
          show "qkd_layer s = qkd_layer t"
            by (subst assms(2,3); simp)+
        qed
        show "kme (snd s) = kme (snd t)"
          by (subst assms(2,3); simp)+
      qed
      show "kme s = kme t"
        by (subst assms(2,3); simp)+
    qed
    show "a \<notin> act SingleHop.kmes_bridges_qkd_layer_network.ioa \<longrightarrow> snd s = snd t"
      unfolding actions_of_par using a_act_netw by fastforce
  qed
qed

lemma trans_in_kme_netw:
  assumes "\<exists>sender msg rcpt. a = Receive sender rcpt msg \<or> a = Send sender rcpt msg"
    and "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, msgs)"
    and "t = (apps app1 app2, kmes kme1' kme2', bridges bridge1 bridge2, qkd, msgs')"
    and "i \<in> c_nodes"
    and kme_trans: "(kme s i, a, kme t i) \<in> trans_of (SingleHop.kme.ioa i)"
    and netw_trans: "(network s, a, network t) \<in> trans_of (SingleHop.network.ioa)"
    and "(i = Node1 \<longrightarrow> kme2 = kme2') \<and> (i = Node2 \<longrightarrow> kme1 = kme1')"
  shows "(s,a,t) \<in> trans_of SingleHop.System.ioa"
proof -
  have a_act_kme: "a \<in> act (SingleHop.kme.ioa i)"
    using kme_trans SingleHop.kme.is_ioa[of i] unfolding Automata.IOA_def is_trans_of_def by fastforce
  have a_in_kmes: "a \<in> act SingleHop.kmes.ioa"
    unfolding actions_of_set_ioa using assms(4) a_act_kme by fast
  have a_act_netw: "a \<in> act SingleHop.network.ioa"
    using netw_trans SingleHop.network.is_trans_of unfolding is_trans_of_def by auto
  show ?thesis
  proof (rule trans_par_inductSnd)
    show "a \<notin> act SingleHop.apps.ioa" 
      unfolding actions_of_set_ioa
      using a_act_kme SingleHop.actsDisj_app_kme assms(4) by fast
    show "a \<in> act SingleHop.kmes_bridges_qkd_layer_network.ioa"
      apply(rule par_actL)
      using a_in_kmes .
    show "snd s \<midarrow>a\<midarrow>SingleHop.kmes_bridges_qkd_layer_network.ioa\<rightarrow> snd t"
    proof (rule trans_par_inductFst_Gen)
      show "a \<in> act SingleHop.kmes.ioa"
        using a_in_kmes .
      show "kme s \<midarrow>a\<midarrow>SingleHop.kmes.ioa\<rightarrow> kme t"
      proof (rule trans_set_ioa_induct[of i])
        show "i \<in> c_nodes" 
          by (rule assms(4))
        show "a \<in> act (SingleHop.kme.ioa i)" 
          by (rule a_act_kme)
        show "kme s i \<midarrow>a\<midarrow>SingleHop.kme.ioa i\<rightarrow> kme t i"
          using assms(5) .
        show "\<forall>ia\<in>c_nodes. ia \<noteq> i \<longrightarrow> a \<notin> act (SingleHop.kme.ioa ia)"
          using SingleHop.actsDisj_kme_kme assms(4) a_act_kme by blast
        show "kme t = (kme s)(i := kme t i)"
          apply(subst assms(2,3); simp add: kmes_def assms(7))+
          using assms(4) unfolding c_nodes_def by fastforce
      qed
      show "a \<in> act SingleHop.bridges_qkd_layer_network.ioa \<longrightarrow>
    snd (snd s) \<midarrow>a\<midarrow>SingleHop.bridges_qkd_layer_network.ioa\<rightarrow> snd (snd t)"
      proof (rule; rule trans_par_inductSnd)
        show "a \<notin> act SingleHop.bridges.ioa"
          unfolding actions_of_set_ioa
          using a_act_kme SingleHop.actsDisj_kme_bridge assms(4) by fast
        show "a \<in> act SingleHop.qkd_layer_network.ioa"
          apply(rule par_actR)
          using a_act_netw .
        show "snd (snd (snd s)) \<midarrow>a\<midarrow>SingleHop.qkd_layer_network.ioa\<rightarrow> snd (snd (snd t))"
        proof (rule trans_par_inductSnd)
          show "a \<notin> act SingleHop.qkd_layer.ioa"
            using a_act_kme SingleHop.actsDisj_kme_qkd assms(4) by fast
          show "a \<in> act SingleHop.network.ioa"
            using a_act_netw .
          show "network s \<midarrow>a\<midarrow>SingleHop.network.ioa\<rightarrow> network t"
            using assms(6) .
          show "qkd_layer s = qkd_layer t"
            by(subst assms(2,3); simp)+
        qed
        show "kme (snd s) = kme (snd t)"
          by(subst assms(2,3); simp)+
      qed
      show "a \<notin> act SingleHop.bridges_qkd_layer_network.ioa \<longrightarrow> snd (snd s) = snd (snd t)"
        unfolding actions_of_par using a_act_netw by fast
    qed
    show "app s = app t"
      by(subst assms(2,3); simp)+
  qed
qed

lemma trans_in_bridge_netw:
  assumes "\<exists>sender msg rcpt. a = Receive sender rcpt msg \<or> a = Send sender rcpt msg"
    and "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, msgs)"
    and "t = (apps app1 app2, kmes kme1 kme2, bridges bridge1' bridge2', qkd, msgs')"
    and "i \<in> c_nodes"
    and "b \<in> c_bridgeIDs i"
    and bridge_trans: "(bridge s i b, a, bridge t i b) \<in> trans_of (SingleHop.bridge.ioa b i)"
    and netw_trans: "(network s, a, network t) \<in> trans_of (SingleHop.network.ioa)"
    and "(i = Node1 \<longrightarrow> bridge2 = bridge2') \<and> (i = Node2 \<longrightarrow> bridge1 = bridge1')"
  shows "(s,a,t) \<in> trans_of SingleHop.System.ioa"
proof -
  have a_act_bridge: "a \<in> act (SingleHop.bridge.ioa b i)"
    using bridge_trans SingleHop.bridge.is_ioa[of b i] unfolding Automata.IOA_def is_trans_of_def by fastforce
  have a_act_netw: "a \<in> act SingleHop.network.ioa"
    using netw_trans SingleHop.network.is_trans_of unfolding is_trans_of_def by auto
  show ?thesis
  proof (rule trans_par_inductSnd)
    show "a \<notin> act SingleHop.apps.ioa"
      unfolding actions_of_set_ioa
      using a_act_bridge SingleHop.actsDisj_app_bridge assms(4,5) by blast
    show "a \<in> act SingleHop.kmes_bridges_qkd_layer_network.ioa"
      apply (rule par_actR; rule par_actL)
      unfolding actions_of_set_ioa
      using a_act_bridge assms(4,5) by fast
    show "snd s \<midarrow>a\<midarrow>SingleHop.kmes_bridges_qkd_layer_network.ioa\<rightarrow> snd t"
    proof (rule trans_par_inductSnd)
      show "a \<notin> act SingleHop.kmes.ioa"
        unfolding actions_of_set_ioa
        using a_act_bridge SingleHop.actsDisj_kme_bridge assms(4,5) by blast
      show "a \<in> act SingleHop.bridges_qkd_layer_network.ioa"
        apply (rule par_actL)
        unfolding actions_of_set_ioa
        using a_act_bridge assms(4,5) by fast
      show "snd (snd s) \<midarrow>a\<midarrow>SingleHop.bridges_qkd_layer_network.ioa\<rightarrow> snd (snd t)"
      proof (rule trans_par_inductFst_Gen)
        show "a \<in> act SingleHop.bridges.ioa"
          unfolding actions_of_set_ioa
          using assms(4,5) a_act_bridge by fast
        show "fst (snd (snd s)) \<midarrow>a\<midarrow>SingleHop.bridges.ioa\<rightarrow> fst (snd (snd t))"
        proof (rule trans_set_ioa_induct[of "(i,b)"])
          show "(i, b) \<in> Sigma c_nodes c_bridgeIDs"
            using assms(4,5) by blast
          show "a \<in> act (case (i, b) of (nodeID, bridgeID) \<Rightarrow> SingleHop.bridge.ioa bridgeID nodeID)"
            using a_act_bridge by fastforce
          show "bridge s i b \<midarrow>a\<midarrow>(case (i, b) of (nodeID, bridgeID) \<Rightarrow> SingleHop.bridge.ioa bridgeID nodeID)\<rightarrow> bridge t i b"
            using assms(6) by fastforce
          show "\<forall>ia\<in>Sigma c_nodes c_bridgeIDs.
            ia \<noteq> (i, b) \<longrightarrow> a \<notin> act (case ia of (nodeID, bridgeID) \<Rightarrow> SingleHop.bridge.ioa bridgeID nodeID)"
          proof (rule; rule)
            fix ia
            assume ia_sigma: "ia \<in> Sigma c_nodes c_bridgeIDs"
            assume ia_neq: "ia \<noteq> (i, b)"
            obtain nodeID bridgeID where split:"ia = (nodeID, bridgeID)"
              by fastforce
            then have "bridgeID \<noteq> b"
              using SingleHop.disjoint_node_bridges ia_sigma assms(4,5) ia_neq apply auto
              unfolding disjnt_def by blast
            moreover have "nodeID \<in> c_nodes"
              using ia_sigma split Sigma_def by blast
            moreover have "bridgeID \<in> c_bridgeIDs nodeID"
              using ia_sigma split Sigma_def by force
            ultimately have "a \<notin> act (SingleHop.bridge.ioa bridgeID nodeID)"
              using a_act_bridge assms(4,5) SingleHop.actsDisj_bridge_bridge[of i nodeID b bridgeID] by blast
            then show "a \<notin> act (case ia of (nodeID, bridgeID) \<Rightarrow> SingleHop.bridge.ioa bridgeID nodeID)"
              using split by fast
          qed
          show "fst (snd (snd t)) = (fst (snd (snd s)))((i, b) := bridge t i b)"
            apply(subst assms(2,3); simp add: bridges_def assms(8))+
            using assms(4,5) unfolding c_nodes_def c_bridgeIDs_def by auto
        qed
        show "a \<in> act SingleHop.qkd_layer_network.ioa \<longrightarrow>
              snd (snd (snd s)) \<midarrow>a\<midarrow>SingleHop.qkd_layer_network.ioa\<rightarrow> snd (snd (snd t))"
        proof(rule; rule trans_par_inductSnd)
          show "a \<notin> act SingleHop.qkd_layer.ioa"
            using a_act_bridge SingleHop.actsDisj_bridge_qkd assms(4,5) by blast
          show "a \<in> act SingleHop.network.ioa"
            using a_act_netw .
          show "network s \<midarrow>a\<midarrow>SingleHop.network.ioa\<rightarrow> network t"
            using netw_trans .
          show "qkd_layer s = qkd_layer t"
            by(subst assms(2,3); simp)+
        qed
        show "a \<notin> act SingleHop.qkd_layer_network.ioa \<longrightarrow> snd (snd (snd s)) = snd (snd (snd t))"
          unfolding actions_of_par using a_act_netw by fastforce
      qed
      show "kme s = kme t"
        by(subst assms(2,3); simp)+
    qed
    show "app s = app t"
      by(subst assms(2,3); simp)+
  qed
qed

lemma trans_in_qkd_netw:
  assumes "\<exists>sender msg rcpt. a = Receive sender rcpt msg \<or> a = Send sender rcpt msg"
    and "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, msgs)"
    and "t = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd', msgs')"
    and qkd_trans: "(qkd_layer s, a, qkd_layer t) \<in> trans_of (SingleHop.qkd_layer.ioa)"
    and netw_trans: "(network s, a, network t) \<in> trans_of (SingleHop.network.ioa)"
  shows "(s,a,t) \<in> trans_of SingleHop.System.ioa"
proof -
  have a_act_qkd: "a \<in> act (SingleHop.qkd_layer.ioa)"
    using qkd_trans SingleHop.qkd_layer.is_trans_of unfolding is_trans_of_def by auto
  have a_act_netw: "a \<in> act SingleHop.network.ioa"
    using netw_trans SingleHop.network.is_trans_of unfolding is_trans_of_def by auto
  show ?thesis
  proof (rule trans_par_inductSnd)
    show "a \<notin> act SingleHop.apps.ioa"
      unfolding actions_of_set_ioa
      using a_act_qkd SingleHop.actsDisj_app_qkd by blast
    show "a \<in> act SingleHop.kmes_bridges_qkd_layer_network.ioa"
      apply (rule par_actR; rule par_actR; rule par_actL)
      using a_act_qkd .
    show "snd s \<midarrow>a\<midarrow>SingleHop.kmes_bridges_qkd_layer_network.ioa\<rightarrow> snd t"
    proof (rule trans_par_inductSnd)
      show "a \<notin> act SingleHop.kmes.ioa"
        unfolding actions_of_set_ioa
        using a_act_qkd SingleHop.actsDisj_kme_qkd by blast
      show "a \<in> act SingleHop.bridges_qkd_layer_network.ioa"
        apply (rule par_actR; rule par_actL)
        using a_act_qkd .
      show "snd (snd s) \<midarrow>a\<midarrow>SingleHop.bridges_qkd_layer_network.ioa\<rightarrow> snd (snd t)"
      proof (rule trans_par_inductSnd)
        show "a \<notin> act SingleHop.bridges.ioa"
          unfolding actions_of_set_ioa
          using a_act_qkd SingleHop.actsDisj_bridge_qkd by fast
        show "a \<in> act SingleHop.qkd_layer_network.ioa"
          apply (rule par_actL)
          using a_act_qkd .
        show "snd (snd (snd s)) \<midarrow>a\<midarrow>SingleHop.qkd_layer_network.ioa\<rightarrow> snd (snd (snd t))"
        proof (rule trans_par_inductFst_Gen)
          show "a \<in> act SingleHop.qkd_layer.ioa"
            using a_act_qkd .
          show "qkd_layer s \<midarrow>a\<midarrow>SingleHop.qkd_layer.ioa\<rightarrow> qkd_layer t"
            using qkd_trans .
          show "a \<in> act SingleHop.network.ioa \<longrightarrow>
                network s \<midarrow>a\<midarrow>SingleHop.network.ioa\<rightarrow> network t"
            using netw_trans by blast
          show "a \<notin> act SingleHop.network.ioa \<longrightarrow> network s = network t"
            using a_act_netw by blast
        qed
        show "kme (snd s) = kme (snd t)"
          by (subst assms(2,3); simp)+
      qed
      show "kme s = kme t"
        by (subst assms(2,3); simp)+
    qed
    show "app s = app t"
      by (subst assms(2,3); simp)+
  qed
qed

end