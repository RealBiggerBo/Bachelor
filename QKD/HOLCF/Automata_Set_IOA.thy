theory Automata_Set_IOA
  imports Automata_IOA Automata_Set_Ext
begin

locale Set_IOA =
  fixes I :: "'i set"
    and g :: "'i \<Rightarrow> ('a, 's) ioa"
  assumes compatible: "pairwise_compatible I g"
      and valid_components: "\<And>i. i \<in> I \<Longrightarrow> Automata.IOA (g i)"
begin

end

sublocale Set_IOA < IOA "set_to_ioa I g"
  rewrites asig_eq:"asig = family_asig I g"
    and starts_eq:"starts = {\<sigma>. \<forall>i\<in>I. \<sigma> i \<in> starts_of (g i)}"
    and trans_eq:"trans = {(\<sigma>, a, \<tau>).
      a \<in> family_actions I g \<and>
      (\<forall>i.
         if i \<in> I \<and> a \<in> actions (asig_of (g i))
         then (\<sigma> i, a, \<tau> i) \<in> trans_of (g i)
         else \<tau> i = \<sigma> i)}"
    and wfair_eq:"wfair = (\<Union>i\<in>I. wfair_of (g i))"
    and sfair_eq:"sfair = (\<Union>i\<in>I. sfair_of (g i))"
  apply(unfold_locales)
proof -
  show "is_asig_of (set_to_ioa I g)"
    unfolding is_asig_of_def is_asig_def asig_projections apply simp
    unfolding family_asig_def family_inputs_def family_outputs_def family_internals_def 
      asig_projections asig_of_def apply auto
    using compatible valid_components
    unfolding pairwise_compatible_def Automata.IOA_def is_asig_of_def is_asig_def asig_of_def apply auto
    unfolding compatible_def asig_projections asig_of_def actions_def apply (auto; fast)
    by (metis asig_inputs_def asig_internals_def asig_of_def comp_eq_dest_lhs compatible disjoint_iff inp_is_act
        intA_is_not_actB pairwise_compatible_def)
next
  show "is_starts_of (set_to_ioa I g)"
    unfolding is_starts_of_def apply simp
  proof -
    have "\<And>i. i \<in> I \<Longrightarrow> starts_of (g i) \<noteq> {}"
      using valid_components by (simp add: Automata.IOA_def is_starts_of_def)
    obtain \<sigma> where sigma_def: "\<sigma> = (\<lambda>i. SOME s. s \<in> starts_of (g i))"
      by simp
    then have sigma_is_start: "\<forall>i\<in>I. \<sigma> i \<in> starts_of (g i)"
      by (simp add: \<open>\<And>i. i \<in> I \<Longrightarrow> starts_of (g i) \<noteq> {}\<close> some_in_eq)
    then show "\<exists>x. \<forall>i\<in>I. x i \<in> starts_of (g i)"
      by blast
  qed
next
  show "is_trans_of (set_to_ioa I g)"
    unfolding is_trans_of_def set_to_ioa_def trans_of_def by (simp add: ioa_triple_proj)
next
  show "input_enabled (set_to_ioa I g)"
    unfolding input_enabled_def
  proof (intro allI impI)
    fix a s1
    assume a_inp: "a \<in> inputs (asig_of (set_to_ioa I g))"
    let ?s2 = "\<lambda>i. if i \<in> I \<and> a \<in> act (g i) then SOME s2. s1 i \<midarrow>a\<midarrow>g i\<rightarrow> s2 else s1 i"
    show "\<exists>s2. s1 \<midarrow>a\<midarrow>(set_to_ioa I g)\<rightarrow> s2"
    proof (rule exI[where x = ?s2])
      have trans: "\<And>i. i \<in> I \<Longrightarrow> a \<in> act (g i) \<Longrightarrow> (s1 i, a, ?s2 i) \<in> trans_of (g i)"
        using act_in_set_is_inp[of I g a] valid_components compatible a_inp
        unfolding Automata.IOA_def input_enabled_def
        by (auto intro: someI_ex)
      show "s1 \<midarrow>a\<midarrow>(set_to_ioa I g)\<rightarrow> ?s2"
        using a_inp trans inp_is_act
        unfolding set_to_ioa_def trans_of_def apply auto
        unfolding family_actions_def family_asig_def
        unfolding family_inputs_def family_outputs_def family_internals_def apply auto
        unfolding asig_projections asig_of_def apply auto
        unfolding actions_def asig_projections by auto
    qed
  qed
  show "asig_of (set_to_ioa I g) = family_asig I g"
    by simp
  show "starts_of (set_to_ioa I g) = {\<sigma>. \<forall>i\<in>I. \<sigma> i \<in> starts_of (g i)} "
    by simp
  show "wfair_of (set_to_ioa I g) = (\<Union>i\<in>I. wfair_of (g i))"
    by simp
  show "sfair_of (set_to_ioa I g) = (\<Union>i\<in>I. sfair_of (g i))"
    by simp
  show "trans_of (set_to_ioa I g) = {(\<sigma>, a, \<tau>). a \<in> family_actions I g \<and> (\<forall>i. if i \<in> I \<and> a \<in> act (g i) then \<sigma> i \<midarrow>a\<midarrow>g i\<rightarrow> \<tau> i else \<tau> i = \<sigma> i)}"
    by simp
qed

end