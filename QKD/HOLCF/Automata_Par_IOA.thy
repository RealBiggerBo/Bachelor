theory Automata_Par_IOA
  imports Automata_IOA
begin

locale Par_IOA =
  A: IOA A + 
  B: IOA B
  for A :: "('a, 's) ioa"
    and B :: "('a, 't) ioa" +
  assumes compatible: "compatible A B"
begin

abbreviation par_trans where
  \<open>par_trans \<equiv> {tr.
        let
          s = fst tr;
          a = fst (snd tr);
          t = snd (snd tr)
        in
          (a \<in> act A \<or> a \<in> act B) \<and>
          (if a \<in> act A then (fst s, a, fst t) \<in> trans_of A
           else fst t = fst s) \<and>
          (if a \<in> act B then (snd s, a, snd t) \<in> trans_of B
           else snd t = snd s)}\<close>

end

sublocale Par_IOA < IOA "A \<parallel> B"
  rewrites asig_eq:"asig_of ioa = asig_comp (asig_of A) (asig_of B)"
     and inp_eq:"inp ioa = (inp A \<union> inp B) - (out A \<union> out B)"
     and out_eq:"out ioa = out A \<union> out B"
     and int_eq:"int ioa = int A \<union> int B"
     and act_eq:"act ioa = act A \<union> act B"
     and starts_eq:"starts_of ioa = {p. fst p \<in> starts_of A \<and> snd p \<in> starts_of B}"
     and trans_eq:"trans_of ioa = par_trans"
     and wfair_eq:"wfair_of ioa = wfair_of A \<union> wfair_of B"
     and sfair_eq:"sfair_of ioa = sfair_of A \<union> sfair_of B"
  apply (unfold_locales)
proof -
  let ?ioa = "A \<parallel> B"
  show "is_asig_of ?ioa"
    using compatible A.is_asig_of B.is_asig_of 
    unfolding is_asig_of_def compatible_def asig_of_def is_asig_def par_def apply simp
    unfolding asig_comp_def asig_projections actions_def by auto
  show "is_starts_of ?ioa"
    using A.is_starts_of B.is_starts_of starts_of_par
    unfolding is_starts_of_def apply auto
  proof -
    fix x :: 's and xa :: 't
    assume a1: "xa \<in> starts_of B"
    assume a2: "starts_of ?ioa = {}"
    obtain bb :: "('a set \<times> 'a set \<times> 'a set) \<times> 't set \<times> ('t \<times> 'a \<times> 't) set \<times> 'a set set \<times> 'a set set \<Rightarrow> ('a set \<times> 'a set \<times> 'a set) \<times> 's set \<times> ('s \<times> 'a \<times> 's) set \<times> 'a set set \<times> 'a set set \<Rightarrow> 's \<times> 't \<Rightarrow> bool" where
      f3: "\<forall>X0 x1 x2. bb X0 x1 x2 = (snd x2 \<in> starts_of X0 \<and> fst x2 \<in> starts_of x1)"
      by moura
    then have "\<forall>p pa. starts_of (pa \<parallel> p) = Collect (bb p pa)"
      using starts_of_par by blast
    then show False
      using f3 a2 a1 by (metis (no_types) A.is_starts_of empty_Collect_eq ex_in_conv fst_eqD is_starts_of_def snd_eqD)
  qed
  show "is_trans_of ?ioa"
    using A.is_trans_of B.is_trans_of trans_of_par by simp
  show "input_enabled ?ioa"
    using compatible A.input_enabled B.input_enabled input_enabled_par by blast
  show "asig_of ?ioa = asig_comp (asig_of A) (asig_of B)"
    unfolding asig_of_def par_def by simp
  show "starts_of ?ioa = {p. fst p \<in> starts_of A \<and> snd p \<in> starts_of B}"
    unfolding starts_of_def par_def by simp
  show in':"inp ?ioa = inp A \<union> inp B - (out A \<union> out B)"
    unfolding par_def asig_of_def asig_inputs_def asig_comp_def by simp
  show out':"out ?ioa = out A \<union> out B"
    unfolding par_def asig_of_def asig_outputs_def asig_comp_def by simp
  show int':"int ?ioa = int A \<union> int B"
    unfolding par_def asig_of_def asig_internals_def asig_comp_def by simp
  show "act ?ioa = act A \<union> act B"
    using in' out' int'
    unfolding actions_def par_def asig_projections asig_comp_def by auto
  show "trans_of ?ioa = par_trans"
    unfolding par_def trans_of_def by simp
  show "wfair_of ?ioa = wfair_of A \<union> wfair_of B"
    unfolding par_def wfair_of_def by simp
  show "sfair_of ?ioa = sfair_of A \<union> sfair_of B"
    unfolding par_def sfair_of_def by simp
qed

end