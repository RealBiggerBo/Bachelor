theory QKD_QKD_Layer
  imports Automata_IOA QKD_Datatypes
begin

inductive qkd_layer_step :: "'proc set \<Rightarrow> ('keyID, 'keyVal, 'proc) qkd_layer_state \<Rightarrow> ('proc, ('keyID, 'keyVal, 'proc) msg) action \<Rightarrow> ('keyID, 'keyVal, 'proc) qkd_layer_state \<Rightarrow> bool" where
  GetKey_Gen:
  \<open>rcpt \<in> qkdIDs \<Longrightarrow>
   keyID \<notin> fst ` ((snd ` gen) \<union> sent) \<Longrightarrow>
   qkd_layer_step qkdIDs 
                  (QKD gen sent) 
                  (Receive sender rcpt (GetKey rcpt target))
                  (QKD (gen \<union> {(sender, keyID, keyVal)}) sent)\<close> |
  Send:
  \<open>sender \<in> qkdIDs \<Longrightarrow>
   (rcpt, keyID, keyVal) \<in> gen ==> 
   qkd_layer_step qkdIDs
                  (QKD gen sent)
                  (Send sender rcpt (KeyResponse keyID keyVal))
                  (QKD (gen - {(rcpt, keyID, keyVal)}) (sent \<union> {(keyID, keyVal)}))\<close> |
  GetKeyWithID_Reserve: (*NOT YET IN PLANTUML*)
  \<open>rcpt \<in> qkdIDs \<Longrightarrow>
   (keyID, keyVal) \<in> sent \<Longrightarrow>
   qkd_layer_step qkdIDs
                  (QKD gen sent)
                  (Receive sender rcpt (GetKeyWithID rcpt target keyID))
                  (QKD (gen \<union> {(sender, keyID, keyVal)}) (sent - {(keyID, keyVal)}))\<close>

locale QKD_Layer_locale =
  fixes qkdIDs :: "'proc set"
begin

definition asig:
  \<open>asig = ({Receive sender qkd msg | sender qkd msg. qkd \<in> qkdIDs}, 
           {Send qkd rcpt msg | qkd rcpt msg. qkd \<in> qkdIDs}, 
           {})\<close>

definition layer_trans:
  \<open>layer_trans = 
    {(s, a, s') | s a s'. qkd_layer_step qkdIDs s a s'}
  \<union> {(s, a, s) | s a. (\<forall>s'. \<not>qkd_layer_step qkdIDs s a s') \<and> a \<in> {Receive sender qkd msg | sender qkd msg. qkd \<in> qkdIDs}}\<close>

sublocale IOA
  "(asig, {QKD {} {}}, layer_trans, {}, {})"
proof
  show "is_asig_of (asig, {QKD {} {}}, layer_trans, {}, {})"
    unfolding is_asig_of_def asig_of_def apply simp
    unfolding is_asig_def asig asig_projections by auto
  show "is_starts_of (asig, {QKD {} {}}, layer_trans, {}, {})"
    unfolding is_starts_of_def starts_of_def by simp
  show "is_trans_of (asig, {QKD {} {}}, layer_trans, {}, {})"
    unfolding is_trans_of_def trans_of_def layer_trans apply simp
    unfolding actions_def asig_projections asig_of_def asig apply auto
    by (erule qkd_layer_step.cases; auto)
  show "input_enabled (asig, {QKD {} {}}, layer_trans, {}, {})"
    unfolding input_enabled_def asig_inputs_def asig_of_def asig apply simp
    unfolding trans_of_def layer_trans by auto
qed

end

end