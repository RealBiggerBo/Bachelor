theory Automata_Network_DIOA
  imports Automata_IOA Automata_Datatypes
begin

locale Network_DIOA = 
  fixes pid:: 'proc
    and ins:: "('proc, msg) action set"
    and start:: "'state"
    and stepf:: "'state \<Rightarrow> ('proc, msg) action \<Rightarrow> 'state \<times> ('proc \<times> msg) set"
  assumes valid_ins: "\<forall>rcpt msg. Send pid rcpt msg \<notin> ins"
begin

abbreviation dioa_asig where "dioa_asig \<equiv> (ins \<union> {Receive q pid m |q m. True}, {Send pid q m |q m. True}, {})"

abbreviation dioa_trans where
"dioa_trans \<equiv> 
    {(IoaState state msgs, a, IoaState state' (msgs \<union> (\<lambda>msg. (pid, msg)) ` sent)) | state state' a msgs sent. (stepf state a = (state', sent)) \<and> a \<in> ins \<union> {Receive q pid m |q m. True}}
  \<union> {(IoaState state msgs, Send pid q msg, IoaState state (msgs - {(pid, q, msg)})) | state msgs q msg. (pid, q, msg) \<in> msgs}"

lemma deterministic:
  assumes s1_trans:"(s, a, s1) \<in> dioa_trans"
    and s2_trans:"(s, a, s2) \<in> dioa_trans"
  shows "s1 = s2"
  using assms valid_ins by auto

end

sublocale Network_DIOA < IOA "(dioa_asig, {IoaState start {}}, dioa_trans, {}, {})"
  rewrites asig_eq:"asig = dioa_asig"
      and starts_eq:"starts = {IoaState start {}}"
      and trans_eq:"trans = dioa_trans"
      and wfair_eq:"wfair = {}"
      and sfair_eq:"sfair = {}"
  apply (unfold_locales)
proof -
  let ?ioa = "(dioa_asig, {IoaState start {}}, dioa_trans, {}, {})"
  show "is_asig_of ?ioa"
    using valid_ins unfolding is_asig_of_def asig_of_def is_asig_def apply simp
    unfolding asig_projections by auto
  show "is_starts_of ?ioa"
    unfolding is_starts_of_def starts_of_def by simp
  show "is_trans_of ?ioa"
    unfolding is_trans_of_def trans_of_def IOA_def trans_def asig_projections apply auto
    unfolding asig_projections actions_def asig_of_def by auto
  show "input_enabled ?ioa"
    unfolding input_enabled_def asig_inputs_def asig_of_def trans_of_def apply auto
    unfolding trans_def apply (metis ioa_state.exhaust old.prod.exhaust)
    by (metis ioa_state.exhaust old.prod.exhaust)
  show "asig_of ?ioa = dioa_asig"
    unfolding asig_of_def by simp
  show "starts_of ?ioa = {IoaState start {}}"
    unfolding starts_of_def by simp
  show "trans_of ?ioa = dioa_trans"
    unfolding trans_of_def by simp
  show "wfair_of ?ioa = {}"
    unfolding wfair_of_def by simp
  show "sfair_of ?ioa = {}"
    unfolding sfair_of_def by simp
qed

end