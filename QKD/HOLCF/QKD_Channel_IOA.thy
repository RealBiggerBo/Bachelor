theory QKD_Channel_IOA          
  imports Automata_IOA QKD_Datatypes
begin

section Channel

locale Channel =
  fixes start:: 'state
    and add_msg:: "'state \<Rightarrow> 'proc \<Rightarrow> 'proc \<Rightarrow> ('keyID, 'keyVal, 'proc) msg \<Rightarrow> 'state"
    and rmv_msg:: "'state \<Rightarrow> 'proc \<Rightarrow> 'proc \<Rightarrow> ('keyID, 'keyVal, 'proc) msg \<Rightarrow> 'state"
    and can_send_msg:: "'state \<Rightarrow> 'proc \<Rightarrow> 'proc \<Rightarrow> ('keyID, 'keyVal, 'proc) msg \<Rightarrow> bool"
begin

abbreviation channel_asig where 
"channel_asig \<equiv> 
   ({Send pid_a pid_b m | pid_a pid_b m. True},
   {Receive pid_a pid_b m | pid_a pid_b m. True},
   {})"

abbreviation channel_trans where
"channel_trans \<equiv> 
    {(state, Send pid_a pid_b m, add_msg state pid_a pid_b m) | state pid_a pid_b m. True}
  \<union> {(state, Receive pid_a pid_b m, rmv_msg state pid_a pid_b m) | state pid_a pid_b m. can_send_msg state pid_a pid_b m}"

sublocale IOA 
  "(channel_asig,
   {start},
   (channel_trans),
   {},
   {})"
  (*rewrites asig_eq:"asig_of ioa = channel_asig"
      and starts_eq:"starts_of ioa = {start}"
      and trans_eq:"trans_of ioa = channel_trans"
      and wfair_eq:"wfair_of ioa = {}"
      and sfair_eq:"sfair_of ioa = {}"*)
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
(*  show "asig_of ?ioa = channel_asig"
    unfolding asig_of_def by simp
  show "starts_of ?ioa = {start}"
    unfolding starts_of_def by simp
  show "trans_of ?ioa = channel_trans"
    unfolding trans_of_def by simp
  show "wfair_of ?ioa = {}"
    unfolding wfair_of_def by simp
  show "sfair_of ?ioa = {}"
    unfolding sfair_of_def by simp*)
qed

end



section Directed_Channel

locale Channel_IOA = 
  fixes pid_a:: 'proc
    and pid_b:: 'proc
    and start:: 'state
    and add_msg:: "'state \<Rightarrow> 'proc \<Rightarrow> 'proc \<Rightarrow> ('keyID, 'keyVal, 'proc) msg \<Rightarrow> 'state"
    and rmv_msg:: "'state \<Rightarrow> 'proc \<Rightarrow> 'proc \<Rightarrow> ('keyID, 'keyVal, 'proc) msg \<Rightarrow> 'state"
    and can_send_msg:: "'state \<Rightarrow> 'proc \<Rightarrow> 'proc \<Rightarrow> ('keyID, 'keyVal, 'proc) msg \<Rightarrow> bool"
begin

abbreviation channel_asig where 
"channel_asig \<equiv> 
   ({Send pid_a pid_b m | m. True} \<union> {Send pid_b pid_a m | m. True},
   {Receive pid_a pid_b m | m. True} \<union> {Receive pid_b pid_a m | m. True},
   {})"

abbreviation channel_trans where
"channel_trans \<equiv> 
    {(state, Send pid_a pid_b m, add_msg state pid_a pid_b m) | state m. True}
  \<union> {(state, Send pid_b pid_a m, add_msg state pid_b pid_a m) | state m. True}
  \<union> {(state, Receive pid_a pid_b m, rmv_msg state pid_a pid_b m) | state m. can_send_msg state pid_a pid_b m}
  \<union> {(state, Receive pid_b pid_a m, rmv_msg state pid_b pid_a m) | state m. can_send_msg state pid_b pid_a m}"

end

sublocale Channel_IOA < IOA 
  "(channel_asig,
   {start},
   (channel_trans),
   {},
   {})"
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
qed

end