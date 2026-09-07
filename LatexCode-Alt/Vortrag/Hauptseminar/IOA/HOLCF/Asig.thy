(*  Title:      HOL/HOLCF/IOA/Asig.thy
    Author:     Olaf Müller, Tobias Nipkow & Konrad Slind
*)

section ‹Action signatures›

theory Asig
imports Main
begin

type_synonym 'a signature = "'a set × 'a set × 'a set"

definition inputs :: "'action signature ⇒ 'action set"
  where asig_inputs_def: "inputs = fst"

definition outputs :: "'action signature ⇒ 'action set"
  where asig_outputs_def: "outputs = fst ∘ snd"

definition internals :: "'action signature ⇒ 'action set"
  where asig_internals_def: "internals = snd ∘ snd"

definition actions :: "'action signature ⇒ 'action set"
  where "actions asig = inputs asig ∪ outputs asig ∪ internals asig"

definition externals :: "'action signature ⇒ 'action set"
  where "externals asig = inputs asig ∪ outputs asig"

definition locals :: "'action signature ⇒ 'action set"
  where "locals asig = internals asig ∪ outputs asig"

definition is_asig :: "'action signature ⇒ bool"
  where "is_asig triple ⟷
    inputs triple ∩ outputs triple = {} ∧
    outputs triple ∩ internals triple = {} ∧
    inputs triple ∩ internals triple = {}"

definition mk_ext_asig :: "'action signature ⇒ 'action signature"
  where "mk_ext_asig triple = (inputs triple, outputs triple, {})"


lemmas asig_projections = asig_inputs_def asig_outputs_def asig_internals_def

lemma asig_triple_proj:
  "outputs (a, b, c) = b ∧
   inputs (a, b, c) = a ∧
   internals (a, b, c) = c"
  by (simp add: asig_projections)

lemma int_and_ext_is_act: "a ∉ internals S ⟹ a ∉ externals S ⟹ a ∉ actions S"
  by (simp add: externals_def actions_def)

lemma ext_is_act: "a ∈ externals S ⟹ a ∈ actions S"
  by (simp add: externals_def actions_def)

lemma int_is_act: "a ∈ internals S ⟹ a ∈ actions S"
  by (simp add: asig_internals_def actions_def)

lemma inp_is_act: "a ∈ inputs S ⟹ a ∈ actions S"
  by (simp add: asig_inputs_def actions_def)

lemma out_is_act: "a ∈ outputs S ⟹ a ∈ actions S"
  by (simp add: asig_outputs_def actions_def)

lemma ext_and_act: "x ∈ actions S ∧ x ∈ externals S ⟷ x ∈ externals S"
  by (fast intro!: ext_is_act)

lemma not_ext_is_int: "is_asig S ⟹ x ∈ actions S ⟹ x ∉ externals S ⟷ x ∈ internals S"
  by (auto simp add: actions_def is_asig_def externals_def)

lemma not_ext_is_int_or_not_act: "is_asig S ⟹ x ∉ externals S ⟷ x ∈ internals S ∨ x ∉ actions S"
  by (auto simp add: actions_def is_asig_def externals_def)

lemma int_is_not_ext:"is_asig S ⟹ x ∈ internals S ⟹ x ∉ externals S"
  by (auto simp add: externals_def actions_def is_asig_def)

end