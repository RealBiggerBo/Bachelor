theory Automata_Par_Helpers
  imports Automata
begin

section Par_Commute

lemma Par_Asig_Commute:
  shows "asig_of (a \<parallel> b) = asig_of (b \<parallel> a)"
  by (simp add: Un_commute asig_comp_def asig_of_par)

lemma Par_Starts_Commute:
  assumes "f = (\<lambda>(a,b). (b,a))"
  shows "starts_of (a \<parallel> b) = {f x | x. x \<in> starts_of (b \<parallel> a)}"
  unfolding starts_of_def par_def apply simp
  using assms by fastforce

lemma Par_Trans_Commute:
  assumes "f = (\<lambda>((a,b),c,(d,e)). ((b,a),c,(e,d)))"
  shows "trans_of (a \<parallel> b) = {f x | x. x \<in> trans_of (b \<parallel> a)}"
  unfolding trans_of_def par_def apply simp
  using assms apply auto
  by blast+

lemma Par_Wfair_Commute:
  shows "wfair_of (a \<parallel> b) = wfair_of (b \<parallel> a)"
  by (simp add: Un_commute wfair_of_def par_def)

lemma Par_Sfair_Commute:
  shows "sfair_of (a \<parallel> b) = sfair_of (b \<parallel> a)"
  by (simp add: Un_commute sfair_of_def par_def)


section Par_Assoc

lemma Par_Asig_Assoc:
  shows "asig_of ((a \<parallel> b) \<parallel> c) = asig_of (a \<parallel> (b \<parallel> c))"
  unfolding asig_of_def par_def apply simp
  unfolding asig_comp_def apply auto
  by (simp add: asig_triple_proj)+

lemma Par_Starts_Assoc:
  assumes "f = (\<lambda>(a,(b,c)). ((a,b),c))"
  shows "starts_of ((a \<parallel> b) \<parallel> c) = {f x | x. x \<in> starts_of (a \<parallel> (b \<parallel> c))}"
  unfolding starts_of_def par_def apply simp
  using assms by fastforce

lemma Par_Trans_Assoc:
  assumes "f = (\<lambda>((a,(b,c)),d,(e,(f,g))). (((a,b),c),d,((e,f),g)))"
  shows "trans_of ((a \<parallel> b) \<parallel> c) = {f x | x. x \<in> trans_of (a \<parallel> (b \<parallel> c))}"
  unfolding assms
  by (force simp add: trans_of_par actions_of_par Let_def prod_eq_iff)

lemma Par_Wfair_Assoc:
  shows "wfair_of ((a \<parallel> b) \<parallel> c) = wfair_of (a \<parallel> (b \<parallel> c))"
  by (simp add: Un_commute wfair_of_def par_def; blast)

lemma Par_Sfair_Assoc:
  shows "sfair_of ((a \<parallel> b) \<parallel> c) = sfair_of (a \<parallel> (b \<parallel> c))"
  by (simp add: Un_commute sfair_of_def par_def; blast)

end