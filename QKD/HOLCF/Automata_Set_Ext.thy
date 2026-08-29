theory Automata_Set_Ext
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

lemmas family = family_inputs_def family_outputs_def family_internals_def family_actions_def family_asig_def

definition pairwise_compatible:: "'i set \<Rightarrow> ('i \<Rightarrow> ('a, 's) ioa) \<Rightarrow> bool" where
"pairwise_compatible I g \<longleftrightarrow> (\<forall>i\<in>I. \<forall>j\<in>I. i \<noteq> j \<longrightarrow> compatible (g i) (g j))"

(*Lynch's condition: action may only occur in finitely many components *)

definition finite_action_participation:: "'i set \<Rightarrow> ('i \<Rightarrow> ('a, 's) ioa) \<Rightarrow> bool" where
"finite_action_participation I g \<longleftrightarrow> (\<forall>a. finite {i \<in> I. a \<in> actions (asig_of (g i))})"

definition lynch_compatible:: "'i set \<Rightarrow> ('i \<Rightarrow> ('a, 's) ioa) \<Rightarrow> bool" where
"lynch_compatible I g \<longleftrightarrow> pairwise_compatible I g \<and> finite_action_participation I g"


definition set_to_ioa:: "'i set \<Rightarrow> ('i \<Rightarrow> ('a, 's) ioa) \<Rightarrow> ('a, 'i \<Rightarrow> 's) ioa" where
"set_to_ioa I g = (family_asig I g,
                    {\<sigma>. \<forall>i\<in>I. \<sigma> i \<in> starts_of (g i)},
                    {(\<sigma>, a, \<tau>).
                      a \<in> family_actions I g \<and>
                          (\<forall>i.
                             if i \<in> I \<and> a \<in> actions (asig_of (g i))
                             then (\<sigma> i, a, \<tau> i) \<in> trans_of (g i)
                             else \<tau> i = \<sigma> i)},
                    (\<Union>i\<in>I. wfair_of (g i)),
                    (\<Union>i\<in>I. sfair_of (g i)))"




section Lemmas

lemma family_actions_asig [simp]:
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

lemma asig_of_set_ioa [simp]:
"asig_of (set_to_ioa I g) = family_asig I g"
  by (simp add: set_to_ioa_def ioa_projections)

lemma starts_of_set_ioa [simp]:
"starts_of (set_to_ioa I g) = {\<sigma>. \<forall>i\<in>I. \<sigma> i \<in> starts_of (g i)}"
  by (simp add: set_to_ioa_def ioa_projections)

lemma trans_of_set_ioa [simp]:
"trans_of (set_to_ioa I g) =
   {(\<sigma>, a, \<tau>).
      a \<in> family_actions I g \<and>
      (\<forall>i.
         if i \<in> I \<and> a \<in> actions (asig_of (g i))
         then (\<sigma> i, a, \<tau> i) \<in> trans_of (g i)
         else \<tau> i = \<sigma> i)}"
  by (simp add: set_to_ioa_def ioa_projections)

lemma wfair_of_set_ioa [simp]:
"wfair_of (set_to_ioa I g) = (\<Union>i\<in>I. wfair_of (g i))"
  by (simp add: set_to_ioa_def ioa_projections)

lemma sfair_of_set_ioa [simp]:
"sfair_of (set_to_ioa I g) = (\<Union>i\<in>I. sfair_of (g i))"
  by (simp add: set_to_ioa_def ioa_projections)

lemma act_in_set_is_inp:
  assumes compatible: "pairwise_compatible I g"
    and valid_components: "\<And>i. i \<in> I \<Longrightarrow> IOA (g i)"
    and a_inp: "a \<in> inputs (asig_of (set_to_ioa I g))"
    and iI: "i \<in> I" 
    and a_act: "a \<in> act (g i)"
  shows "a \<in> inp (g i)"
proof -
  have "a \<notin> out (g i)"
    using assms apply simp
    unfolding asig_projections family_asig_def family_inputs_def family_outputs_def asig_of_def by auto
  moreover have "a \<notin> int (g i)"
    using assms compatible valid_components 
    unfolding set_to_ioa_def family_asig_def family_inputs_def asig_projections apply auto
    unfolding asig_of_def family_outputs_def family_inputs_def pairwise_compatible_def apply auto
    unfolding asig_projections actions_def apply auto
    unfolding compatible_def asig_projections asig_of_def actions_def apply auto
    unfolding Automata.IOA_def is_asig_of_def is_asig_def asig_of_def asig_projections apply auto
    unfolding input_enabled_def asig_projections trans_of_def asig_of_def is_trans_of_def apply auto
    unfolding is_starts_of_def starts_of_def actions_def asig_projections apply auto
    by (metis Int_iff inf_sup_absorb)
  ultimately show "a \<in> inp (g i)"
    using a_act unfolding actions_def by blast
qed

lemma set_trans_dest: 
  assumes "(s, a, t) \<in> trans_of (set_to_ioa I g)"
  shows "\<exists>i \<in> I. a \<in> act (g i)"
  using assms
  unfolding trans_of_def set_to_ioa_def apply simp
  by (simp add: family_actions_def)

end