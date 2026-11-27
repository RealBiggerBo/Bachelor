theory QKD_System_ActsDisj
  imports QKD_System_Def
begin

context QKD_Network 
begin

section NetworklessActs

lemma actsDisj_app_app:
  assumes "i \<in> nodes"
    and "j \<in> nodes"
    and "i \<noteq> j"
  shows "act (app.ioa i) \<inter> act (app.ioa j) = {}"
  unfolding actions_def asig_projections asig_of_def
  using inj_app assms unfolding inj_on_def by (auto)

lemma actsDisj_app_kme:
  assumes "i \<in> nodes"
    and "j \<in> nodes"
  shows "act (app.ioa i) \<inter> act (kme.ioa j) = {}"
  unfolding actions_def apply simp
  unfolding asig_projections asig_of_def apply simp
  using disjoint_ids unfolding disjnt_def by auto

lemma actsDisj_app_bridge:
  assumes "i \<in> nodes"
    and "j \<in> nodes"
    and "b \<in> bridgeIDs j"
  shows "act (app.ioa i) \<inter> act (bridge.ioa b j) = {}"
  unfolding actions_def apply simp
  unfolding asig_projections asig_of_def apply simp
  using disjoint_ids assms unfolding disjnt_def by fast

lemma actsDisj_app_qkd:
  assumes "i \<in> nodes"
  shows "act (app.ioa i) \<inter> act qkd_layer.ioa = {}"
  unfolding actions_def qkd_layer.asig apply simp
  unfolding asig_projections asig_of_def apply simp
  using disjoint_ids unfolding disjnt_def apply auto
  by fast+

lemma actsDisj_kme_kme:
  assumes "i \<in> nodes"
    and "j \<in> nodes"
    and "i \<noteq> j"
  shows "act (kme.ioa i) \<inter> act (kme.ioa j) = {}"
  unfolding actions_def asig_projections asig_of_def
  using inj_kme assms unfolding inj_on_def by auto

lemma actsDisj_kme_bridge:
  assumes "i \<in> nodes"
    and "j \<in> nodes"
    and "b \<in> bridgeIDs j"
  shows "act (kme.ioa i) \<inter> act (bridge.ioa b j) = {}"
  unfolding actions_def apply simp
  unfolding asig_projections asig_of_def apply simp
  using disjoint_ids assms unfolding disjnt_def by fast

lemma actsDisj_kme_qkd:
  assumes "i \<in> nodes"
  shows "act (kme.ioa i) \<inter> act qkd_layer.ioa = {}"
  unfolding actions_def qkd_layer.asig apply simp
  unfolding asig_projections asig_of_def apply simp
  using disjoint_ids unfolding disjnt_def apply auto
  by fast+

lemma actsDisj_bridge_bridge:
  assumes "i \<in> nodes"
    and "j \<in> nodes"
    and "b1 \<in> bridgeIDs i"
    and "b2 \<in> bridgeIDs j"
    and "b1 \<noteq> b2"
  shows "act (bridge.ioa b1 i) \<inter> act (bridge.ioa b2 j) = {}"
  unfolding actions_def asig_projections asig_of_def
  using assms by auto

lemma actsDisj_bridge_qkd:
  assumes "i \<in> nodes"
    and "b \<in> bridgeIDs i"
  shows "act (bridge.ioa b i) \<inter> act qkd_layer.ioa = {}"
  unfolding actions_def qkd_layer.asig apply simp
  unfolding asig_projections asig_of_def apply simp
  using disjoint_ids unfolding disjnt_def apply auto
  by (metis IntI UNIV_I UN_I assms(2) empty_iff imageI)+


section NetworkActs

lemma acts_app_netw:
  assumes "i \<in> nodes"
  shows "act (app.ioa i) \<inter> act network.ioa = {Send (appID i) rcpt msg | rcpt msg. True} \<union> {Receive sender (appID i) msg | sender msg. True}"
proof -
  let ?A = "inp (app.ioa i)"
  let ?B = "out (app.ioa i)"
  let ?C = "int (app.ioa i)"
  let ?D = "inp network.ioa"
  let ?E = "out network.ioa"
  let ?F = "int network.ioa"
  have "?C = {} \<and> ?F = {}"
    unfolding asig_projections asig_of_def by auto
  then have "(?A \<union> ?B \<union> ?C) \<inter> (?D \<union> ?E \<union> ?F) = (?A \<union> ?B) \<inter> (?D \<union> ?E)"
    by blast
  moreover have "... = ((?A \<union> ?B) \<inter> ?D) \<union> ((?A \<union> ?B) \<inter> ?E)"
    by blast
  ultimately have "(?A \<union> ?B \<union> ?C) \<inter> (?D \<union> ?E \<union> ?F) = ((?A \<inter> ?D) \<union> (?B \<inter> ?D)) \<union> ((?A \<inter> ?E) \<union> (?B \<inter> ?E))"
    by blast
  moreover have "?B \<inter> ?E = {}"
    unfolding asig_projections asig_of_def by auto
  moreover have "?A \<inter> ?D = {}"
    unfolding asig_projections asig_of_def by auto
  ultimately have I:"(?A \<union> ?B \<union> ?C) \<inter> (?D \<union> ?E \<union> ?F) = (?B \<inter> ?D) \<union> (?A \<inter> ?E)"
    by blast
  have "?B \<inter> ?D = {Send (appID i) rcpt msg | rcpt msg. True}"
    unfolding asig_projections asig_of_def apply simp
    using assms(1) by blast
  moreover have "?A \<inter> ?E = {Receive sender (appID i) msg | sender msg. True}"
    unfolding asig_projections asig_of_def apply simp
    using assms(1) by blast
  ultimately have II:"(?B \<inter> ?D) \<union> (?A \<inter> ?E) = {Send (appID i) rcpt msg | rcpt msg. True} \<union> {Receive sender (appID i) msg | sender msg. True}"
    by blast
  have "(?A \<union> ?B \<union> ?C) \<inter> (?D \<union> ?E \<union> ?F) = {Send (appID i) rcpt msg | rcpt msg. True} \<union> {Receive sender (appID i) msg | sender msg. True}"
    apply(subst I)
    using II . 
  then show ?thesis
    unfolding actions_def by blast
qed

lemma acts_kme_netw:
  assumes "i \<in> nodes"
  shows "act (kme.ioa i) \<inter> act network.ioa = {Send (kmeID i) rcpt msg | rcpt msg. True} \<union> {Receive sender (kmeID i) msg | sender msg. True}"
proof -
  let ?A = "inp (kme.ioa i)"
  let ?B = "out (kme.ioa i)"
  let ?C = "int (kme.ioa i)"
  let ?D = "inp network.ioa"
  let ?E = "out network.ioa"
  let ?F = "int network.ioa"
  have "?C = {} \<and> ?F = {}"
    unfolding asig_projections asig_of_def by auto
  then have "(?A \<union> ?B \<union> ?C) \<inter> (?D \<union> ?E \<union> ?F) = (?A \<union> ?B) \<inter> (?D \<union> ?E)"
    by blast
  moreover have "... = ((?A \<union> ?B) \<inter> ?D) \<union> ((?A \<union> ?B) \<inter> ?E)"
    by blast
  ultimately have "(?A \<union> ?B \<union> ?C) \<inter> (?D \<union> ?E \<union> ?F) = ((?A \<inter> ?D) \<union> (?B \<inter> ?D)) \<union> ((?A \<inter> ?E) \<union> (?B \<inter> ?E))"
    by blast
  moreover have "?B \<inter> ?E = {}"
    unfolding asig_projections asig_of_def by auto
  moreover have "?A \<inter> ?D = {}"
    unfolding asig_projections asig_of_def by auto
  ultimately have I:"(?A \<union> ?B \<union> ?C) \<inter> (?D \<union> ?E \<union> ?F) = (?B \<inter> ?D) \<union> (?A \<inter> ?E)"
    by blast
  have "?B \<inter> ?D = {Send (kmeID i) rcpt msg | rcpt msg. True}"
    unfolding asig_projections asig_of_def apply simp
    using assms(1) by blast
  moreover have "?A \<inter> ?E = {Receive sender (kmeID i) msg | sender msg. True}"
    unfolding asig_projections asig_of_def apply simp
    using assms(1) by blast
  ultimately have II:"(?B \<inter> ?D) \<union> (?A \<inter> ?E) = {Send (kmeID i) rcpt msg | rcpt msg. True} \<union> {Receive sender (kmeID i) msg | sender msg. True}"
    by blast
  have "(?A \<union> ?B \<union> ?C) \<inter> (?D \<union> ?E \<union> ?F) = {Send (kmeID i) rcpt msg | rcpt msg. True} \<union> {Receive sender (kmeID i) msg | sender msg. True}"
    apply(subst I)
    using II . 
  then show ?thesis
    unfolding actions_def by blast
qed

lemma acts_bridge_netw:
  assumes "i \<in> nodes"
    and "b \<in> bridgeIDs i"
  shows "act (bridge.ioa b i) \<inter> act network.ioa = {Send b rcpt msg | rcpt msg. True} \<union> {Receive sender b msg | sender msg. True}"
proof -
  let ?A = "inp (bridge.ioa b i)"
  let ?B = "out (bridge.ioa b i)"
  let ?C = "int (bridge.ioa b i)"
  let ?D = "inp network.ioa"
  let ?E = "out network.ioa"
  let ?F = "int network.ioa"
  have "?C = {} \<and> ?F = {}"
    unfolding asig_projections asig_of_def by auto
  then have "(?A \<union> ?B \<union> ?C) \<inter> (?D \<union> ?E \<union> ?F) = (?A \<union> ?B) \<inter> (?D \<union> ?E)"
    by blast
  moreover have "... = ((?A \<union> ?B) \<inter> ?D) \<union> ((?A \<union> ?B) \<inter> ?E)"
    by blast
  ultimately have "(?A \<union> ?B \<union> ?C) \<inter> (?D \<union> ?E \<union> ?F) = ((?A \<inter> ?D) \<union> (?B \<inter> ?D)) \<union> ((?A \<inter> ?E) \<union> (?B \<inter> ?E))"
    by blast
  moreover have "?B \<inter> ?E = {}"
    unfolding asig_projections asig_of_def by auto
  moreover have "?A \<inter> ?D = {}"
    unfolding asig_projections asig_of_def by auto
  ultimately have I:"(?A \<union> ?B \<union> ?C) \<inter> (?D \<union> ?E \<union> ?F) = (?B \<inter> ?D) \<union> (?A \<inter> ?E)"
    by blast
  have "?B \<inter> ?D = {Send b rcpt msg | rcpt msg. True}"
    unfolding asig_projections asig_of_def apply simp
    using assms(1,2) by blast
  moreover have "?A \<inter> ?E = {Receive sender b msg | sender msg. True}"
    unfolding asig_projections asig_of_def apply simp
    using assms(1,2) by blast
  ultimately have II:"(?B \<inter> ?D) \<union> (?A \<inter> ?E) = {Send b rcpt msg | rcpt msg. True} \<union> {Receive sender b msg | sender msg. True}"
    by blast
  have "(?A \<union> ?B \<union> ?C) \<inter> (?D \<union> ?E \<union> ?F) = {Send b rcpt msg | rcpt msg. True} \<union> {Receive sender b msg | sender msg. True}"
    apply(subst I)
    using II . 
  then show ?thesis
    unfolding actions_def by blast
qed

lemma acts_qkd_netw:
  shows "act qkd_layer.ioa \<inter> act network.ioa = {Send sender rcpt msg | sender rcpt msg. sender \<in> qkdID ` (\<Union>(bridgeIDs ` nodes))} \<union> {Receive sender rcpt msg | sender rcpt msg. rcpt \<in> qkdID ` (\<Union>(bridgeIDs ` nodes))}"
proof -
  let ?A = "inp (qkd_layer.ioa)"
  let ?B = "out (qkd_layer.ioa)"
  let ?C = "int (qkd_layer.ioa)"
  let ?D = "inp network.ioa"
  let ?E = "out network.ioa"
  let ?F = "int network.ioa"
  have "?C = {} \<and> ?F = {}"
    unfolding asig_projections asig_of_def qkd_layer.asig by auto
  then have "(?A \<union> ?B \<union> ?C) \<inter> (?D \<union> ?E \<union> ?F) = (?A \<union> ?B) \<inter> (?D \<union> ?E)"
    by blast
  moreover have "... = ((?A \<union> ?B) \<inter> ?D) \<union> ((?A \<union> ?B) \<inter> ?E)"
    by blast
  ultimately have "(?A \<union> ?B \<union> ?C) \<inter> (?D \<union> ?E \<union> ?F) = ((?A \<inter> ?D) \<union> (?B \<inter> ?D)) \<union> ((?A \<inter> ?E) \<union> (?B \<inter> ?E))"
    by blast
  moreover have "?B \<inter> ?E = {}"
    unfolding asig_projections asig_of_def qkd_layer.asig by auto
  moreover have "?A \<inter> ?D = {}"
    unfolding asig_projections asig_of_def qkd_layer.asig by auto
  ultimately have I:"(?A \<union> ?B \<union> ?C) \<inter> (?D \<union> ?E \<union> ?F) = (?B \<inter> ?D) \<union> (?A \<inter> ?E)"
    by blast
  have "?B \<inter> ?D = {Send sender rcpt msg | sender rcpt msg. sender \<in> qkdID ` (\<Union>(bridgeIDs ` nodes))}"
    unfolding asig_projections asig_of_def qkd_layer.asig by auto
  moreover have "?A \<inter> ?E = {Receive sender rcpt msg | sender rcpt msg. rcpt \<in> qkdID ` (\<Union>(bridgeIDs ` nodes))}"
    unfolding asig_projections asig_of_def qkd_layer.asig by auto
  ultimately have II:"(?B \<inter> ?D) \<union> (?A \<inter> ?E) = {Send sender rcpt msg | sender rcpt msg. sender \<in> qkdID ` (\<Union>(bridgeIDs ` nodes))} \<union> {Receive sender rcpt msg | sender rcpt msg. rcpt \<in> qkdID ` (\<Union>(bridgeIDs ` nodes))}"
    by metis
  have "(?A \<union> ?B \<union> ?C) \<inter> (?D \<union> ?E \<union> ?F) = {Send sender rcpt msg | sender rcpt msg. sender \<in> qkdID ` (\<Union>(bridgeIDs ` nodes))} \<union> {Receive sender rcpt msg | sender rcpt msg. rcpt \<in> qkdID ` (\<Union>(bridgeIDs ` nodes))}"
    apply(subst I)
    using II . 
  then show ?thesis
    unfolding actions_def by blast
qed

lemma acts_only_netw:
  assumes "all = (appID ` nodes) \<union> (kmeID ` nodes) \<union> \<Union>(bridgeIDs ` nodes) \<union> qkdID ` (\<Union>(bridgeIDs ` nodes))"
    and "a \<in> act System.ioa"
    and "a \<notin> act apps.ioa"
    and "a \<notin> act kmes.ioa"
    and "a \<notin> act bridges.ioa"
    and "a \<notin> act qkd_layer.ioa"
  shows "a \<in> {Send sender rcpt msg | sender rcpt msg. sender \<notin> all} \<union>
             {Receive sender rcpt msg | sender rcpt msg. rcpt \<notin> all}"
proof -
  have step: "a \<in> act network.ioa - act apps.ioa - act kmes.ioa - act bridges.ioa - act qkd_layer.ioa"
    using assms(2-6) unfolding actions_of_par by fast
  have eq: "act network.ioa - act apps.ioa - act kmes.ioa - act bridges.ioa - act qkd_layer.ioa = 
            {Send sender rcpt msg | sender rcpt msg. sender \<notin> all} \<union>
            {Receive sender rcpt msg | sender rcpt msg. rcpt \<notin> all}"
    using assms(1) apply simp
    unfolding actions_def asig_projections asig_of_def family qkd_layer.asig apply simp
    apply (rule set_eqI)
    apply (simp only: Un_iff Diff_iff mem_Collect_eq UN_iff image_iff)
    apply (case_tac x)
    apply (simp_all)
    by blast+
  from step eq show ?thesis by blast
qed

end

end