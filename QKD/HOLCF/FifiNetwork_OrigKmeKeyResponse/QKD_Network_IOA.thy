theory QKD_Network_IOA
  imports Automata_IOA QKD_Datatypes
begin

locale Network_IOA = 
  fixes pid:: 'proc
    and ins:: "('proc, ('keyID, 'keyVal, 'proc) msg) action set"
    and start:: "'state"
    and step_rel:: "'state \<Rightarrow> ('proc, ('keyID, 'keyVal, 'proc) msg) action \<Rightarrow> 'state \<Rightarrow> ('proc \<times> ('keyID, 'keyVal, 'proc) msg) set \<Rightarrow> bool"
  assumes valid_ins: "\<forall>rcpt msg. Send pid rcpt msg \<notin> ins"
begin

abbreviation ioa_asig where "ioa_asig \<equiv> (ins \<union> {Receive q pid m |q m. True}, {Send pid q m |q m. True}, {})"

abbreviation ioa_trans where
"ioa_trans \<equiv> 
    {(IoaState state msgs, a, IoaState state' (msgs \<union> (\<lambda>msg. (pid, msg)) ` sent)) | state state' a msgs sent. (step_rel state a state' sent) \<and> a \<in> ins \<union> {Receive q pid m |q m. True}}
  \<union> {(IoaState state msgs, a, IoaState state msgs) | state a msgs. (\<forall>state' sent. \<not>step_rel state a state' sent) \<and> a \<in> ins \<union> {Receive q pid m |q m. True}}
  \<union> {(IoaState state msgs, Send pid q msg, IoaState state (msgs - {(pid, q, msg)})) | state msgs q msg. (pid, q, msg) \<in> msgs}"

end

sublocale Network_IOA < IOA "(ioa_asig, {IoaState start {}}, ioa_trans, {}, {})"
  (*rewrites asig_eq:"asig_of ioa = ioa_asig"
      and starts_eq:"starts_of ioa = {IoaState start {}}"
      and trans_eq:"trans_of ioa = ioa_trans"
      and wfair_eq:"wfair_of ioa = {}"
      and sfair_eq:"sfair_of ioa = {}"*)
  apply (unfold_locales)
proof -
  let ?ioa = "(ioa_asig, {IoaState start {}}, ioa_trans, {}, {})"
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
    unfolding trans_def apply (metis ioa_state.exhaust)
    by (metis ioa_state.exhaust)
  (*show "asig_of ?ioa = ioa_asig"
    unfolding asig_of_def by simp
  show "starts_of ?ioa = {IoaState start {}}"
    unfolding starts_of_def by simp
  show "trans_of ?ioa = ioa_trans"
    unfolding trans_of_def by simp
  show "wfair_of ?ioa = {}"
    unfolding wfair_of_def by simp
  show "sfair_of ?ioa = {}"
    unfolding sfair_of_def by simp*)
qed

end