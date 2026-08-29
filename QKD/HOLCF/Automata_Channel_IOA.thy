theory Automata_Channel_IOA
  imports Automata_IOA Automata_Datatypes
begin

locale DirectedChannel_IOA = 
  fixes pid_sender:: 'proc
    and pid_rcpt:: 'proc
    and start:: "'state"
    and add_msg:: "'state \<Rightarrow> msg \<Rightarrow> 'state"
    and rmv_msg:: "'state \<Rightarrow> msg \<Rightarrow> 'state"
    and can_send_msg:: "'state \<Rightarrow> msg \<Rightarrow> bool"
begin

abbreviation channel_asig where "channel_asig \<equiv> ({Send pid_sender pid_rcpt m | m. True}, {Receive pid_sender pid_rcpt m | m. True}, {})"

abbreviation channel_trans where
"channel_trans \<equiv> 
    {(state, Send pid_sender pid_rcpt m, add_msg state m) | state m. True}
  \<union> {(state, Receive pid_sender pid_rcpt m, rmv_msg state m) | state m. can_send_msg state m}"  

end

sublocale DirectedChannel_IOA < IOA 
  "(channel_asig,
   {start},
   (channel_trans),
   {},
   {})"
  rewrites asig_eq:"asig = channel_asig"
      and starts_eq:"starts = {start}"
      and trans_eq:"trans = channel_trans"
      and wfair_eq:"wfair = {}"
      and sfair_eq:"sfair = {}"
  apply (unfold_locales)
proof -
  let ?ioa = "(channel_asig, {start}, channel_trans, {}, {})"
  show "is_asig_of ?ioa"
    unfolding is_asig_of_def asig_of_def is_asig_def asig_projections by auto
  show "is_starts_of ?ioa"
    unfolding is_starts_of_def starts_of_def by simp
  show "is_trans_of ?ioa"
    unfolding is_trans_of_def trans_of_def trans_def asig_projections apply auto
    unfolding asig_projections actions_def asig_of_def by auto
  show "input_enabled ?ioa"
    unfolding input_enabled_def asig_projections asig_of_def trans_of_def by auto
  show "asig_of ?ioa = channel_asig"
    unfolding asig_of_def by simp
  show "starts_of ?ioa = {start}"
    unfolding starts_of_def by simp
  show "trans_of ?ioa = channel_trans"
    unfolding trans_of_def by simp
  show "wfair_of ?ioa = {}"
    unfolding wfair_of_def by simp
  show "sfair_of ?ioa = {}"
    unfolding sfair_of_def by simp
qed

end