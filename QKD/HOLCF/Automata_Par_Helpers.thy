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

section ProofTactics

lemma compatibleParR:
  shows "compatible A (B \<parallel> C) \<longleftrightarrow> compatible A B \<and> compatible A C"
  unfolding compatible_def outputs_of_par internals_of_par actions_of_par by auto

lemma compatibleParL:
  shows "compatible (A \<parallel> B) C \<longleftrightarrow> compatible A C \<and> compatible B C"
  unfolding compatible_def outputs_of_par internals_of_par actions_of_par by auto

lemma starts_of_par_split[case_names "startsA" "startsB"]:
  assumes startsA: "starts_of A = {a}"
  assumes startsB: "starts_of B = {b}"
  shows "starts_of (A \<parallel> B) = {(a,b)}"
  unfolding starts_of_par
  using assms by fastforce

lemma trans_par_inductL:
  assumes "a \<in> act A"
    and "(s1, a, t1) \<in> trans_of A"
    and "a \<notin> act B"
  shows "((s1,s2),a,(t1,s2)) \<in> trans_of (A \<parallel> B)"
  apply(subst trans_of_par)
  using assms by force

lemma trans_par_inductFst:
  assumes "a \<in> act A"
    and "(fst s, a, fst t) \<in> trans_of A"
    and "a \<notin> act B"
    and "snd s = snd t"
  shows "(s,a,t) \<in> trans_of (A \<parallel> B)"
  apply(subst trans_of_par)
  using assms by simp

lemma trans_par_inductFst_Gen:
  assumes "a \<in> act A"
    and "(fst s, a, fst t) \<in> trans_of A"
    and "a \<in> act B \<longrightarrow> snd s \<midarrow>a\<midarrow>B\<rightarrow> snd t"
    and "a \<notin> act B \<longrightarrow> snd s = snd t"
  shows "(s,a,t) \<in> trans_of (A \<parallel> B)"
  apply(subst trans_of_par)
  using assms by simp

lemma trans_par_inductR:
  assumes "a \<notin> act A"
    and "a \<in> act B"
    and "(s2, a, t2) \<in> trans_of B"
  shows "((s1,s2),a,(s1,t2)) \<in> trans_of (A \<parallel> B)"
  apply(subst trans_of_par)
  using assms by force

lemma trans_par_inductSnd:
  assumes "a \<notin> act A"
    and "a \<in> act B"
    and "(snd s, a, snd t) \<in> trans_of B"
    and "fst s = fst t"
  shows "(s, a, t) \<in> trans_of (A \<parallel> B)"
  apply(subst trans_of_par)
  using assms by simp

lemma trans_par_inductSnd_Gen:
  assumes "a \<notin> act A \<longrightarrow> fst s = fst t"
    and "a \<in> act A \<longrightarrow> fst s \<midarrow>a\<midarrow>A\<rightarrow> fst t"
    and "a \<in> act B"
    and "(snd s, a, snd t) \<in> trans_of B"
  shows "(s,a,t) \<in> trans_of (A \<parallel> B)"
  apply(subst trans_of_par)
  using assms by simp

lemma no_par_act:
  assumes "a \<notin> act A"
    and "a \<notin> act B"
  shows "a \<notin> act (A \<parallel> B)"
  unfolding actions_of_par
  using assms by simp

lemma par_actL:
  assumes "a \<in> act A"
  shows "a \<in> act (A \<parallel> B)"
  unfolding actions_of_par
  using assms by simp

lemma par_actR:
  assumes "a \<in> act B"
  shows "a \<in> act (A \<parallel> B)"
  unfolding actions_of_par
  using assms by simp

lemma par_trans_elim:
  assumes "s \<midarrow>a\<midarrow>(A \<parallel> B)\<rightarrow> t"
  shows "(a \<in> act A \<longrightarrow> fst s \<midarrow>a\<midarrow>A\<rightarrow> fst t) \<and>
         (a \<notin> act A \<longrightarrow> fst s = fst t) \<and>
         (a \<in> act B \<longrightarrow> snd s \<midarrow>a\<midarrow>B\<rightarrow> snd t) \<and>
         (a \<notin> act B \<longrightarrow> snd s = snd t)"
  using assms unfolding trans_of_par by simp

end