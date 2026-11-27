theory Automata_Set_Par
  imports Automata_Set_Ext
begin

section Set_of_Par

lemma asig_of_set_to_ioa_par:
  assumes "g = (\<lambda>i. a i \<parallel> b i)"
  shows "asig_of (set_to_ioa I g) = asig_of ((set_to_ioa I a) \<parallel> (set_to_ioa I b))"
  apply(subst assms)
  unfolding asig_of_set_ioa asig_of_par asig_comp_def family_asig_def apply simp
  unfolding asig_projections apply simp
  unfolding family inputs_of_par outputs_of_par internals_of_par by auto

lemma starts_of_set_to_ioa_par:
  assumes "g = (\<lambda>i. a i \<parallel> b i)"
    and "f = (\<lambda>(sa, sb). (\<lambda>i. (sa i, sb i)))"
  shows "starts_of (set_to_ioa I g) = {f x | x. x \<in> starts_of ((set_to_ioa I a) \<parallel> (set_to_ioa I b))}"
  apply(subst assms)+
  unfolding starts_of_par starts_of_set_ioa apply simp
  unfolding starts_of_def apply simp
  by force

lemma trans_of_set_to_ioa_par:
  assumes "g = (\<lambda>i. a i \<parallel> b i)"
    and "f = (\<lambda>(sa, sb). (\<lambda>i. (sa i, sb i)))"
    and "tf = (\<lambda>(s,a,t). (f s, a, f t))"
  shows "trans_of (set_to_ioa I g) = {tf x | x. x \<in> trans_of ((set_to_ioa I a) \<parallel> (set_to_ioa I b))}"
proof (rule set_eqI, rule iffI)
  fix tr
  assume "tr \<in> trans_of (set_to_ioa I g)"
  then obtain \<sigma> act \<tau> where tr_eq: "tr = (\<sigma>, act, \<tau>)" 
    by (cases tr, auto)
  have "tr \<in> {tf x | x. x \<in> trans_of ((set_to_ioa I a) \<parallel> (set_to_ioa I b))}"
  proof -
    (* Provide the exact existential witness to Isabelle *)
    let ?sa = "\<lambda>i. fst (\<sigma> i)"
    let ?sb = "\<lambda>i. snd (\<sigma> i)"
    let ?ta = "\<lambda>i. fst (\<tau> i)"
    let ?tb = "\<lambda>i. snd (\<tau> i)"
    let ?witness = "((?sa, ?sb), act, (?ta, ?tb))"
    have "tf ?witness = tr" 
      using tr_eq unfolding assms by auto
    moreover have "?witness \<in> trans_of ((set_to_ioa I a) \<parallel> (set_to_ioa I b))"
      using \<open>tr \<in> trans_of (set_to_ioa I g)\<close> tr_eq
      unfolding assms trans_of_set_ioa trans_of_par family_actions_def actions_of_par apply simp
      unfolding family Let_def apply simp
      apply (simp_all split: if_splits)
      by (metis prod.collapse)
    ultimately show ?thesis by blast
  qed
  then show "tr \<in> {tf x | x. x \<in> trans_of ((set_to_ioa I a) \<parallel> (set_to_ioa I b))}" .
next
  fix tr
  assume "tr \<in> {tf x | x. x \<in> trans_of ((set_to_ioa I a) \<parallel> (set_to_ioa I b))}"
  then obtain x where "tr = tf x" and "x \<in> trans_of ((set_to_ioa I a) \<parallel> (set_to_ioa I b))"
    by blast
  then obtain s_x act_x t_x where "x = (s_x, act_x, t_x)" 
    by (cases x, auto)
  then obtain sa sb ta tb where x_eq: "x = ((sa, sb), act_x, (ta, tb))" 
    by (cases s_x, cases t_x, auto)
  have tr_eq: "tr = ((\<lambda>i. (sa i, sb i)), act_x, (\<lambda>i. (ta i, tb i)))"
    using \<open>tr = tf x\<close> x_eq unfolding assms by auto
  show "tr \<in> trans_of (set_to_ioa I g)"
    using \<open>x \<in> trans_of ((set_to_ioa I a) \<parallel> (set_to_ioa I b))\<close> x_eq tr_eq
    unfolding assms trans_of_set_ioa trans_of_par family_actions_def actions_of_par apply simp
    unfolding family Let_def apply auto
    by (simp_all split: if_splits)
qed

lemma wfair_of_set_to_ioa_par:
  assumes "g = (\<lambda>i. a i \<parallel> b i)"
  shows "wfair_of (set_to_ioa I g) = wfair_of ((set_to_ioa I a) \<parallel> (set_to_ioa I b))"
  apply(subst assms)
  unfolding wfair_of_def par_def set_to_ioa_def apply simp
  by blast

lemma sfair_of_set_to_ioa_par:
  assumes "g = (\<lambda>i. a i \<parallel> b i)"
  shows "sfair_of (set_to_ioa I g) = sfair_of ((set_to_ioa I a) \<parallel> (set_to_ioa I b))"
  apply(subst assms)
  unfolding sfair_of_def par_def set_to_ioa_def apply simp
  by blast


section Nested_set_ioa

lemma asig_set_to_ioa_nested_sigma:
  fixes I :: "'i set"
    and f :: "'i \<Rightarrow> 'j set"
    and g :: "'i \<Rightarrow> 'j \<Rightarrow> ('a, 's) ioa"
  shows "asig_of (set_to_ioa I (\<lambda>i. set_to_ioa (f i) (g i))) =
         asig_of (set_to_ioa (Sigma I f) (\<lambda>(i, j). g i j))"
  unfolding asig_of_set_ioa
  unfolding family inputs_of_set_ioa outputs_of_set_ioa internals_of_set_ioa Sigma_def
  by auto

lemma starts_of_set_to_ioa_nested_sigma:
  assumes "f_state = (\<lambda>s. (\<lambda>i j. s (i, j)))"
  shows "starts_of (set_to_ioa I (\<lambda>i. set_to_ioa (f i) (g i))) =
         {f_state s | s. s \<in> starts_of (set_to_ioa (Sigma I f) (\<lambda>(i, j). g i j))}"
  apply(subst assms)
  unfolding starts_of_set_ioa Sigma_def apply simp
  apply auto
  by (metis case_prod_conv)

lemma trans_of_set_to_ioa_nested_sigma:
  assumes "f_state = (\<lambda>s. (\<lambda>i j. s (i, j)))"
    and "tf = (\<lambda>(s, a, t). (f_state s, a, f_state t))"
  shows "trans_of (set_to_ioa I (\<lambda>i. set_to_ioa (f i) (g i))) =
         {tf x | x. x \<in> trans_of (set_to_ioa (Sigma I f) (\<lambda>(i, j). g i j))}"
  proof (rule set_eqI, rule iffI)
  fix tr
  assume "tr \<in> trans_of (set_to_ioa I (\<lambda>i. set_to_ioa (f i) (g i)))"
  then obtain \<sigma> act \<tau> where tr_eq: "tr = (\<sigma>, act, \<tau>)"
    by (cases tr, auto)
  have "tr \<in> {tf x | x. x \<in> trans_of (set_to_ioa (Sigma I f) (\<lambda>(i, j). g i j))}"
  proof -
    let ?s = "\<lambda>(i, j). \<sigma> i j"
    let ?t = "\<lambda>(i, j). \<tau> i j"
    let ?witness = "(?s, act, ?t)"
    have "tf ?witness = tr"
      using tr_eq unfolding assms by auto
    moreover have "?witness \<in> trans_of (set_to_ioa (Sigma I f) (\<lambda>(i, j). g i j))"
      using \<open>tr \<in> trans_of (set_to_ioa I (\<lambda>i. set_to_ioa (f i) (g i)))\<close> tr_eq
      unfolding trans_of_set_ioa family_actions_def Sigma_def
      apply simp
      apply (auto split: if_splits)
      unfolding family apply simp
       apply metis
      apply simp
      by blast
    ultimately show ?thesis by blast
  qed
  then show "tr \<in> {tf x | x. x \<in> trans_of (set_to_ioa (Sigma I f) (\<lambda>(i, j). g i j))}" .
next
  fix tr
  assume "tr \<in> {tf x | x. x \<in> trans_of (set_to_ioa (Sigma I f) (\<lambda>(i, j). g i j))}"
  then obtain x where "tr = tf x" and "x \<in> trans_of (set_to_ioa (Sigma I f) (\<lambda>(i, j). g i j))"
    by blast
  then obtain s_x act_x t_x where x_eq: "x = (s_x, act_x, t_x)"
    by (cases x, auto)
  have tr_eq: "tr = (\<lambda>i j. s_x (i, j), act_x, \<lambda>i j. t_x (i, j))"
    using \<open>tr = tf x\<close> x_eq unfolding assms by auto
  show "tr \<in> trans_of (set_to_ioa I (\<lambda>i. set_to_ioa (f i) (g i)))"
    using \<open>x \<in> trans_of (set_to_ioa (Sigma I f) (\<lambda>(i, j). g i j))\<close> x_eq tr_eq
    unfolding trans_of_set_ioa family_actions_def Sigma_def
    apply simp
    apply (auto split: if_splits)
    unfolding family_actions_def apply simp_all
    by blast+
qed

lemma wfair_of_set_to_ioa_nested_sigma:
  shows "wfair_of (set_to_ioa I (\<lambda>i. set_to_ioa (f i) (g i))) =
         wfair_of (set_to_ioa (Sigma I f) (\<lambda>(i, j). g i j))"
  unfolding wfair_of_def set_to_ioa_def Sigma_def
  by auto

lemma sfair_of_set_to_ioa_nested_sigma:
  shows "sfair_of (set_to_ioa I (\<lambda>i. set_to_ioa (f i) (g i))) =
         sfair_of (set_to_ioa (Sigma I f) (\<lambda>(i, j). g i j))"
  unfolding sfair_of_def set_to_ioa_def Sigma_def
  by auto

end