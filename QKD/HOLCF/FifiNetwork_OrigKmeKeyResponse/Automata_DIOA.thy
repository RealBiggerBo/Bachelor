theory Automata_DIOA
  imports Automata_IOA
begin

datatype ('state, 'msg) ioa_state = IoaState (IoaState_curState: 'state) (IoaState_msgBuffer: "'msg set")

locale DIOA = 
  fixes pid:: 'proc
    and ins:: "'action set"
    and outs:: "'action set"
    and ints:: "'action set"
    and start:: "'state"
    and stepf:: "'state \<Rightarrow> 'action \<Rightarrow> 'state \<times> ('proc \<times> 'msg) set"
    and mk_msg:: "'action \<Rightarrow> ('proc \<times> 'proc \<times> 'msg) option"
  assumes valid_sig: "is_asig (ins, outs, ints)"
      and valid_outs: "\<And>a msg. mk_msg a = Some msg \<Longrightarrow> a \<in> outs"
begin

definition asig where "asig = (ins, outs, ints)"

definition trans where
"trans = 
    {(IoaState state msgs, a, IoaState state' (msgs \<union> (\<lambda>msg. (pid, msg)) ` sent)) | state state' a msgs sent. (stepf state a = (state', sent)) \<and> a \<in> (ins \<union> ints)}
  \<union> {(IoaState state msgs, a, IoaState state (msgs - {msg})) | state msgs a msg. msg \<in> msgs \<and> mk_msg a = Some msg}"

definition dioa where "dioa = (asig, {IoaState start {}}, trans, {}, {})"

lemma is_asig: "is_asig_of dioa"
  using valid_sig unfolding dioa_def is_asig_of_def asig_def asig_of_def by simp

lemma is_start: "is_starts_of dioa"
  unfolding is_starts_of_def dioa_def starts_of_def by simp

lemma is_trans:
  "is_trans_of dioa"
  unfolding is_trans_of_def trans_of_def DIOA_def dioa_def trans_def asig_projections apply auto
  unfolding asig_def asig_projections actions_def asig_of_def apply auto
  using valid_outs by blast

lemma is_input_enabled:
  "input_enabled dioa"
  unfolding input_enabled_def DIOA_def asig_projections asig_of_def trans_of_def apply auto
  unfolding dioa_def asig_def trans_def apply auto
  by (metis ioa_state.exhaust surj_pair)

lemma is_ioa:
  shows "Automata.IOA dioa"
  unfolding Automata.IOA_def
  using is_asig is_start is_trans is_input_enabled by metis
end

sublocale DIOA < IOA
  ins
  outs
  ints
  "{IoaState start {}}"
  trans
  "{}"
  "{}"
proof
  show "is_asig_of ((ins, outs, ints), {IoaState start {}}, local.trans, {}, {})"
    by (metis asig_def is_asig dioa_def)
  show "is_starts_of ((ins, outs, ints), {IoaState start {}}, local.trans, {}, {})"
    by (metis asig_def dioa_def is_start)
  show "is_trans_of ((ins, outs, ints), {IoaState start {}}, local.trans, {}, {})"
    by (metis asig_def dioa_def is_trans)
  show "input_enabled ((ins, outs, ints), {IoaState start {}}, local.trans, {}, {})"
    by (metis asig_def dioa_def is_input_enabled)
qed


end