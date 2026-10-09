theory QKD_Interpretation_4Hop_Trans_Helpers
  imports QKD_Interpretation_Line_4Hop
begin

lemma trans_in_kme_no_netw:
  assumes "\<forall>sender receiver msg. a \<noteq> Send sender receiver msg"
    and "\<forall>sender receiver msg. a \<noteq> Receive sender receiver msg"
    and "s = (apps app1 app2 app3 app4, kmes kme1 kme2 kme3 kme4, bridges bridge1_2 bridge2_1 bridge2_3 bridge3_2 bridge3_4 bridge4_3, qkd, msgs)"
    and "t = (apps app1 app2 app3 app4, kmes kme1' kme2' kme3' kme4', bridges bridge1_2 bridge2_1 bridge2_3 bridge3_2 bridge3_4 bridge4_3, qkd, msgs)"
    and "i \<in> c_nodes"
    and kme_trans: "(kme s i, a, kme t i) \<in> trans_of (Line4Hop.kme.ioa i)"
    and "(i = Node1 \<longrightarrow> kme2 = kme2' \<and> kme3 = kme3' \<and> kme4 = kme4') \<and> 
          (i = Node2 \<longrightarrow> kme1 = kme1' \<and> kme3 = kme3' \<and> kme4 = kme4') \<and>
          (i = Node3 \<longrightarrow> kme1 = kme1' \<and> kme2 = kme2' \<and> kme4 = kme4') \<and>
          (i = Node4 \<longrightarrow> kme1 = kme1' \<and> kme2 = kme2' \<and> kme3 = kme3')"
  shows "(s,a,t) \<in> trans_of Line4Hop.System.ioa"
proof -
  have a_act_kme: "a \<in> act (Line4Hop.kme.ioa i)"
    using kme_trans Line4Hop.kme.is_ioa[of i] unfolding Automata.IOA_def is_trans_of_def by fastforce
  have a_in_kmes: "a \<in> act Line4Hop.kmes.ioa"
    unfolding actions_of_set_ioa using assms(5) a_act_kme by blast
  show ?thesis
  proof (rule trans_par_inductSnd)
    show "a \<notin> act Line4Hop.apps.ioa" 
      unfolding actions_of_set_ioa
      using a_act_kme Line4Hop.actsDisj_app_kme assms(5) by fast
    show "a \<in> act Line4Hop.kmes_bridges_qkd_layer_network.ioa"
      apply(rule par_actL)
      using a_in_kmes .
    show "snd s \<midarrow>a\<midarrow>Line4Hop.kmes_bridges_qkd_layer_network.ioa\<rightarrow> snd t"
    proof (rule trans_par_inductFst)
      show "a \<in> act Line4Hop.kmes.ioa"
        using a_in_kmes .
      show "kme s \<midarrow>a\<midarrow>Line4Hop.kmes.ioa\<rightarrow> kme t"
      proof(rule trans_set_ioa_induct)
        show "i \<in> c_nodes"
          using assms(5) .
        show "a \<in> act (Line4Hop.kme.ioa i)"
          using a_act_kme .
        show "kme s i \<midarrow>a\<midarrow>Line4Hop.kme.ioa i\<rightarrow> kme t i"
          using assms(6) .
        show "\<forall>ia\<in>c_nodes. ia \<noteq> i \<longrightarrow> a \<notin> act (Line4Hop.kme.ioa ia)"
          using Line4Hop.actsDisj_kme_kme assms(5) a_act_kme by blast
        show "kme t = (kme s)(i := kme t i)"
          apply(subst assms(3,4); simp add: kmes_def assms(7))+
          using assms(5) unfolding c_nodes_def by auto
      qed
      show "a \<notin> act Line4Hop.bridges_qkd_layer_network.ioa"
        apply (rule no_par_act)
        unfolding actions_of_set_ioa
        using a_act_kme Line4Hop.actsDisj_kme_bridge assms(5) apply fast
        apply (rule no_par_act)
        using a_act_kme Line4Hop.actsDisj_kme_qkd assms(5) apply fast
      proof
        assume "a \<in> act Line4Hop.network.ioa"
        then have "a \<in> act (Line4Hop.kme.ioa i) \<inter> act Line4Hop.network.ioa"
          using a_act_kme by simp
        then have "\<And>all. all = c_appID ` c_nodes \<union> c_kmeID ` c_nodes \<union> \<Union> (c_bridgeIDs ` c_nodes) \<union> c_qkdID ` \<Union> (c_bridgeIDs ` c_nodes) \<Longrightarrow>
                        a \<in> {Send (c_kmeID i) rcpt msg |rcpt msg. rcpt \<in> all} \<union> 
                            {Receive sender (c_kmeID i) msg |sender msg. sender \<in> all}"
          using assms(5) Line4Hop.acts_kme_netw by blast
        then show False
          using assms(1,2) by fastforce
      qed
      show "snd (snd s) = snd (snd t)"
        by(subst assms(3,4); simp)+
    qed
    show "app s = app t"
      by(subst assms(3,4); auto)+
  qed
qed

lemma trans_in_kme_netw:
  assumes "\<exists>sender msg rcpt. a = Receive sender rcpt msg \<or> a = Send sender rcpt msg"
    and "s = (apps app1 app2 app3 app4, kmes kme1 kme2 kme3 kme4, bridges bridge1_2 bridge2_1 bridge2_3 bridge3_2 bridge3_4 bridge4_3, qkd, msgs)"
    and "t = (apps app1 app2 app3 app4, kmes kme1' kme2' kme3' kme4', bridges bridge1_2 bridge2_1 bridge2_3 bridge3_2 bridge3_4 bridge4_3, qkd, msgs')"
    and "i \<in> c_nodes"
    and kme_trans: "(kme s i, a, kme t i) \<in> trans_of (Line4Hop.kme.ioa i)"
    and netw_trans: "(network s, a, network t) \<in> trans_of (Line4Hop.network.ioa)"
    and "(i = Node1 \<longrightarrow> kme2 = kme2' \<and> kme3 = kme3' \<and> kme4 = kme4') \<and> 
          (i = Node2 \<longrightarrow> kme1 = kme1' \<and> kme3 = kme3' \<and> kme4 = kme4') \<and>
          (i = Node3 \<longrightarrow> kme1 = kme1' \<and> kme2 = kme2' \<and> kme4 = kme4') \<and>
          (i = Node4 \<longrightarrow> kme1 = kme1' \<and> kme2 = kme2' \<and> kme3 = kme3')"
  shows "(s,a,t) \<in> trans_of Line4Hop.System.ioa"
proof -
  have a_act_kme: "a \<in> act (Line4Hop.kme.ioa i)"
    using kme_trans Line4Hop.kme.is_ioa[of i] unfolding Automata.IOA_def is_trans_of_def by fastforce
  have a_in_kmes: "a \<in> act Line4Hop.kmes.ioa"
    unfolding actions_of_set_ioa using assms(4) a_act_kme by fast
  have a_act_netw: "a \<in> act Line4Hop.network.ioa"
    using netw_trans Line4Hop.network.is_trans_of unfolding is_trans_of_def by auto
  show ?thesis
  proof (rule trans_par_inductSnd)
    show "a \<notin> act Line4Hop.apps.ioa" 
      unfolding actions_of_set_ioa
      using a_act_kme Line4Hop.actsDisj_app_kme assms(4) by fast
    show "a \<in> act Line4Hop.kmes_bridges_qkd_layer_network.ioa"
      apply(rule par_actL)
      using a_in_kmes .
    show "snd s \<midarrow>a\<midarrow>Line4Hop.kmes_bridges_qkd_layer_network.ioa\<rightarrow> snd t"
    proof (rule trans_par_inductFst_Gen)
      show "a \<in> act Line4Hop.kmes.ioa"
        using a_in_kmes .
      show "kme s \<midarrow>a\<midarrow>Line4Hop.kmes.ioa\<rightarrow> kme t"
      proof (rule trans_set_ioa_induct[of i])
        show "i \<in> c_nodes" 
          by (rule assms(4))
        show "a \<in> act (Line4Hop.kme.ioa i)" 
          by (rule a_act_kme)
        show "kme s i \<midarrow>a\<midarrow>Line4Hop.kme.ioa i\<rightarrow> kme t i"
          using assms(5) .
        show "\<forall>ia\<in>c_nodes. ia \<noteq> i \<longrightarrow> a \<notin> act (Line4Hop.kme.ioa ia)"
          using Line4Hop.actsDisj_kme_kme assms(4) a_act_kme by blast
        show "kme t = (kme s)(i := kme t i)"
          apply(subst assms(2,3); simp add: kmes_def assms(7))+
          using assms(4) unfolding c_nodes_def by fastforce
      qed
      show "a \<in> act Line4Hop.bridges_qkd_layer_network.ioa \<longrightarrow>
    snd (snd s) \<midarrow>a\<midarrow>Line4Hop.bridges_qkd_layer_network.ioa\<rightarrow> snd (snd t)"
      proof (rule; rule trans_par_inductSnd)
        show "a \<notin> act Line4Hop.bridges.ioa"
          unfolding actions_of_set_ioa
          using a_act_kme Line4Hop.actsDisj_kme_bridge assms(4) by fast
        show "a \<in> act Line4Hop.qkd_layer_network.ioa"
          apply(rule par_actR)
          using a_act_netw .
        show "snd (snd (snd s)) \<midarrow>a\<midarrow>Line4Hop.qkd_layer_network.ioa\<rightarrow> snd (snd (snd t))"
        proof (rule trans_par_inductSnd)
          show "a \<notin> act Line4Hop.qkd_layer.ioa"
            using a_act_kme Line4Hop.actsDisj_kme_qkd assms(4) by fast
          show "a \<in> act Line4Hop.network.ioa"
            using a_act_netw .
          show "network s \<midarrow>a\<midarrow>Line4Hop.network.ioa\<rightarrow> network t"
            using assms(6) .
          show "qkd_layer s = qkd_layer t"
            by(subst assms(2,3); simp)+
        qed
        show "kme (snd s) = kme (snd t)"
          by(subst assms(2,3); simp)+
      qed
      show "a \<notin> act Line4Hop.bridges_qkd_layer_network.ioa \<longrightarrow> snd (snd s) = snd (snd t)"
        unfolding actions_of_par using a_act_netw by fast
    qed
    show "app s = app t"
      by(subst assms(2,3); simp)+
  qed
qed

end