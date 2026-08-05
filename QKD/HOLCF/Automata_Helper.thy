theory Automata_Helper
  imports Automata
begin

definition family_inputs:: "'i set \<Rightarrow> ('i \<Rightarrow> ('a, 's) ioa) \<Rightarrow> 'a set" where
"family_inputs I g = (\<Union>i\<in>I. inputs (asig_of (g i)))"

definition family_outputs:: "'i set \<Rightarrow> ('i \<Rightarrow> ('a, 's) ioa) \<Rightarrow> 'a set" where
"family_outputs I g = (\<Union>i\<in>I. outputs (asig_of (g i)))"

definition family_internals:: "'i set \<Rightarrow> ('i \<Rightarrow> ('a, 's) ioa) \<Rightarrow> 'a set" where
"family_internals I g = (\<Union>i\<in>I. internals (asig_of (g i)))"

definition family_actions:: "'i set \<Rightarrow> ('i \<Rightarrow> ('a, 's) ioa) \<Rightarrow> 'a set" where
"family_actions I g = (\<Union>i\<in>I. actions (asig_of (g i)))"

definition family_asig:: "'i set \<Rightarrow> ('i \<Rightarrow> ('a, 's) ioa) \<Rightarrow> 'a signature" where
"family_asig I g = ( family_inputs I g - family_outputs I g,
                     family_outputs I g, 
                     family_internals I g)"

definition pairwise_compatible:: "'i set \<Rightarrow> ('i \<Rightarrow> ('a, 's) ioa) \<Rightarrow> bool" where
"pairwise_compatible I g \<longleftrightarrow> (\<forall>i\<in>I. \<forall>j\<in>I. i \<noteq> j \<longrightarrow> compatible (g i) (g j))"

(*Lynch's condition: action may only occur in finitely many components *)

definition finite_action_participation:: "'i set \<Rightarrow> ('i \<Rightarrow> ('a, 's) ioa) \<Rightarrow> bool" where
"finite_action_participation I g \<longleftrightarrow> (\<forall>a. finite {i \<in> I. a \<in> actions (asig_of (g i))})"

definition lynch_compatible:: "'i set \<Rightarrow> ('i \<Rightarrow> ('a, 's) ioa) \<Rightarrow> bool" where
"lynch_compatible I g \<longleftrightarrow> pairwise_compatible I g \<and> finite_action_participation I g"


definition set_to_ioa:: "'i set \<Rightarrow> ('i \<Rightarrow> ('a, 's) ioa) \<Rightarrow> ('a, 'i \<Rightarrow> 's) ioa" where
"set_to_ioa I g = ( family_asig I g,
                    {\<sigma>. \<forall>i\<in>I. \<sigma> i \<in> starts_of (g i)},
                    {(\<sigma>, a, \<tau>).
                      a \<in> family_actions I g \<and>
                          (\<forall>i.
                             if i \<in> I \<and> a \<in> actions (asig_of (g i))
                             then (\<sigma> i, a, \<tau> i) \<in> trans_of (g i)
                             else \<tau> i = \<sigma> i)},
                    (\<Union>i\<in>I. wfair_of (g i)),
                    (\<Union>i\<in>I. sfair_of (g i)))"

(*Helper lemmas*)
lemma family_actions_asig:
"actions (family_asig I g) = family_actions I g"
  unfolding family_asig_def
            family_inputs_def
            family_outputs_def
            family_internals_def
            family_actions_def
            actions_def
            asig_inputs_def
            asig_outputs_def
            asig_internals_def
  by auto

lemma asig_of_gen_ioa [simp]:
"asig_of (set_to_ioa I g) = family_asig I g"
  by (simp add: set_to_ioa_def ioa_projections)

lemma starts_of_gen_ioa [simp]:
"starts_of (set_to_ioa I g) = {\<sigma>. \<forall>i\<in>I. \<sigma> i \<in> starts_of (g i)}"
  by (simp add: set_to_ioa_def ioa_projections)

lemma trans_of_gen_ioa [simp]:
"trans_of (set_to_ioa I g) =
   {(\<sigma>, a, \<tau>).
      a \<in> family_actions I g \<and>
      (\<forall>i.
         if i \<in> I \<and> a \<in> actions (asig_of (g i))
         then (\<sigma> i, a, \<tau> i) \<in> trans_of (g i)
         else \<tau> i = \<sigma> i)}"
  by (simp add: set_to_ioa_def ioa_projections)

lemma wfair_of_gen_ioa [simp]:
"wfair_of (set_to_ioa I g) = (\<Union>i\<in>I. wfair_of (g i))"
  by (simp add: set_to_ioa_def ioa_projections)

lemma sfair_of_gen_ioa [simp]:
"sfair_of (set_to_ioa I g) = (\<Union>i\<in>I. sfair_of (g i))"
  by (simp add: set_to_ioa_def ioa_projections)

theorem IOA_set_to_ioa:
  assumes compatible: "pairwise_compatible I g"
  assumes components: "\<And>i. i \<in> I \<Longrightarrow> IOA (g i)"
  shows "IOA (set_to_ioa I g)"
proof -
  have component_asig: "i \<in> I \<Longrightarrow> is_asig_of (g i)" 
    for i using components[of i] unfolding IOA_def by blast
  have component_starts: "i \<in> I \<Longrightarrow> is_starts_of (g i)"
    for i using components[of i] unfolding IOA_def by blast
  have component_input_enabled: "i \<in> I \<Longrightarrow> input_enabled (g i)" 
    for i using components[of i] unfolding IOA_def by blast
  have compatible_components: "i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> i \<noteq> j \<Longrightarrow> compatible (g i) (g j)"
    for i j using compatible unfolding pairwise_compatible_def by blast
  have outputs_internals_disjoint: "(\<Union>i\<in>I. out (g i)) \<inter> (\<Union>i\<in>I. int (g i)) = {}"
    proof (rule equals0I)
      fix x
      assume "x \<in> (\<Union>i\<in>I. out (g i)) \<inter> (\<Union>i\<in>I. int (g i))"
      then obtain i j where
        iI: "i \<in> I" and
        jI: "j \<in> I" and
        xout: "x \<in> out (g i)" and
        xint: "x \<in> int (g j)"
        by auto
      show False
      proof (cases "i = j")
        case True
        show False
          using component_asig[OF iI] xout xint True
          unfolding is_asig_of_def is_asig_def
          by (auto simp: asig_projections)
      next
        case False
        have "compatible (g i) (g j)"
          using compatible_components[OF iI jI False] .
        show False
          unfolding compatible_def actions_def
          using xout xint
          by (meson \<open>compatible (g i) (g j)\<close> compat_commute intA_is_not_actB out_is_act)
      qed
    qed
  have inputs_internals_disjoint: "(\<Union>i\<in>I. inp (g i)) \<inter> (\<Union>i\<in>I. int (g i)) = {}"
    proof (rule equals0I)
      fix x
      assume "x \<in> (\<Union>i\<in>I. inp (g i)) \<inter> (\<Union>i\<in>I. int (g i))"
      then obtain i j where
        iI: "i \<in> I" and
        jI: "j \<in> I" and
        xinp: "x \<in> inp (g i)" and
        xint: "x \<in> int (g j)"
        by auto
      show False
      proof (cases "i = j")
        case True
        show False
          unfolding is_asig_of_def is_asig_def
          using component_asig[OF iI] xinp xint True
          by (metis Int_iff empty_iff is_asig_def is_asig_of_def)
      next
        case False
        have "compatible (g i) (g j)"
          using compatible_components[OF iI jI False] .
        show False
          unfolding compatible_def actions_def
          using xinp xint
          by (meson \<open>compatible (g i) (g j)\<close> compat_commute inp_is_act intA_is_not_actB)
      qed
    qed
  have family_actions_eq: "actions (family_asig I g) = family_actions I g"
    unfolding family_asig_def family_actions_def family_inputs_def family_outputs_def
    unfolding family_internals_def actions_def asig_projections
    by auto
  show ?thesis
    unfolding IOA_def
  proof (intro conjI)
    have family_asig_ok: "is_asig (family_asig I g)"
      using outputs_internals_disjoint inputs_internals_disjoint
      unfolding family_asig_def family_inputs_def
      by (auto simp: asig_projections family_outputs_def family_internals_def is_asig_def)
    then show "is_asig_of (set_to_ioa I g)"
      unfolding set_to_ioa_def is_asig_of_def asig_of_def by simp
  next
    have start_exists: "\<And>i. i \<in> I \<Longrightarrow> \<exists>s. s \<in> starts_of (g i)"
      using component_starts unfolding is_starts_of_def by blast
    obtain \<sigma> where sigma_def: "\<sigma> = (\<lambda>i. SOME s. s \<in> starts_of (g i))"
      by simp
    have sigma_is_start: "\<forall>i\<in>I. \<sigma> i \<in> starts_of (g i)"
    proof
      fix i
      assume "i \<in> I"
      have "\<exists>s. s \<in> starts_of (g i)"
        using start_exists[of i] \<open>i \<in> I\<close> by blast
      then show "\<sigma> i \<in> starts_of (g i)"
        unfolding sigma_def by (rule someI_ex)
    qed
    have "starts_of (set_to_ioa I g) \<noteq> {}"
    proof (rule notI)
      assume "starts_of (set_to_ioa I g) = {}"
      moreover have "\<sigma> \<in> starts_of (set_to_ioa I g)"
        using sigma_is_start by simp
      ultimately show False
        by auto
    qed
    then show "is_starts_of (set_to_ioa I g)"
      unfolding is_starts_of_def by simp
  next
    show "is_trans_of (set_to_ioa I g)"
      unfolding is_trans_of_def set_to_ioa_def trans_of_def
      using family_actions_eq
      by (simp add: ioa_triple_proj)
  next
    show "input_enabled (set_to_ioa I g)"
    unfolding input_enabled_def
    proof (intro allI impI allI)
      fix a
      assume a_global: "a \<in> inputs (asig_of (set_to_ioa I g))"
      fix \<sigma>
      have a_global':
        "a \<in> inputs (family_asig I g)"
        unfolding set_to_ioa_def
        using a_global by fastforce
      have a_family_action:
        "a \<in> family_actions I g"
        using a_global'
        unfolding
          family_asig_def
          family_actions_def
          family_inputs_def
          family_outputs_def
          family_internals_def
          asig_projections
          actions_def
        by auto
      obtain \<tau> where
        tau_def: "\<tau> = (\<lambda>i.
          if i \<in> I \<and> a \<in> actions (asig_of (g i))
          then SOME s2. (\<sigma> i, a, s2) \<in> trans_of (g i)
          else \<sigma> i)"
        by simp
      have tau_local: "\<And>i. i \<in> I \<and> a \<in> actions (asig_of (g i)) \<Longrightarrow> (\<sigma> i, a, \<tau> i) \<in> trans_of (g i)"
      proof -
        fix i
        assume i_cond: "i \<in> I \<and> a \<in> actions (asig_of (g i))"
        have global_input_is_local_input:
          "a \<in> inputs (family_asig I g) \<Longrightarrow>
           i \<in> I \<Longrightarrow>
           a \<in> actions (asig_of (g i)) \<Longrightarrow>
           a \<in> inputs (asig_of (g i))"
          proof -
            fix a i
            assume a_global: "a \<in> inputs (family_asig I g)"
            assume iI: "i \<in> I"
            assume a_act_i: "a \<in> actions (asig_of (g i))"
            have a_in_some_input: "\<exists>j\<in>I. a \<in> inputs (asig_of (g j))"
              using a_global
              unfolding family_asig_def family_inputs_def family_outputs_def asig_projections
              by auto
            obtain j where
              jI: "j \<in> I" and
              a_in_j: "a \<in> inputs (asig_of (g j))"
              using a_in_some_input by auto
            show "a \<in> inputs (asig_of (g i))"
            proof (cases "i = j")
              case True
              with a_in_j
              show ?thesis
                by simp
            next
              case False
              have a_not_global_output: "a \<notin> outputs (asig_of (g i))"
                using a_global
                unfolding family_asig_def family_outputs_def asig_projections
                using iI by simp
              show ?thesis
              proof (rule ccontr)
                assume a_not_input: "a \<notin> inputs (asig_of (g i))"
                have a_int_i: "a \<in> internals (asig_of (g i))"
                  using a_act_i a_not_input a_not_global_output
                  unfolding actions_def by auto
                have comp: "compatible (g i) (g j)"
                  using compatible_components[OF iI jI False] .
                have a_act_j: "a \<in> actions (asig_of (g j))"
                  using a_in_j
                  unfolding actions_def
                  by auto
                have False
                  using comp a_int_i a_act_j
                  unfolding compatible_def
                  by auto
                then show False
                  by simp
              qed
            qed
          qed
        have iI: "i \<in> I"
          using i_cond by simp
        have a_act_i: "a \<in> actions (asig_of (g i))"
          using i_cond by simp
        have a_inp_i: "a \<in> inputs (asig_of (g i))"
          using global_input_is_local_input a_global' iI a_act_i by simp
        have enabled_i: "\<forall>s1. \<exists>s2. (s1, a, s2) \<in> trans_of (g i)"
          using component_input_enabled[OF iI] a_inp_i
          unfolding input_enabled_def
          by blast
        have exists_successor: "\<exists>s2. (\<sigma> i, a, s2) \<in> trans_of (g i)"
          using enabled_i by fastforce
        show "(\<sigma> i, a, \<tau> i) \<in> trans_of (g i)"
          unfolding tau_def by (simp; meson exists_successor i_cond some_eq_imp)
      qed
      have tau_spec:
        "\<forall>i.
          (if i \<in> I \<and> a \<in> actions (asig_of (g i))
           then (\<sigma> i, a, \<tau> i) \<in> trans_of (g i)
           else \<tau> i = \<sigma> i)"
      proof
        fix i
        show
          "(if i \<in> I \<and> a \<in> actions (asig_of (g i))
           then (\<sigma> i, a, \<tau> i) \<in> trans_of (g i)
           else \<tau> i = \<sigma> i)"
        using tau_local tau_def by simp
      qed
      show "\<exists>s2. (\<sigma>, a, s2) \<in> trans_of (set_to_ioa I g)"
      proof (rule exI[where x = \<tau>])
        show "(\<sigma>, a, \<tau>) \<in> trans_of (set_to_ioa I g)"
          unfolding set_to_ioa_def trans_of_def
          using a_family_action tau_spec
          by (smt (verit, best) case_prodI ioa_triple_proj mem_Collect_eq sfair_of_def trans_of_def)
      qed
    qed
  qed
qed

end