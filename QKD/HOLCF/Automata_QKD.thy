theory Automata_QKD
  imports Automata
begin

(* --- Datatypes --- *)
datatype ('proc, 'status, 'key, 'id) msg = 
    GetStatus 'proc 
  | Status 'status
  | GetKey 'proc
  | Key "('id \<times> 'key) set"
  | KeyId "'id set"
  | GetKeyWithId "'id set"

datatype ('proc, 'msg) action = 
    Start 'proc 'proc
  | Send 'proc 'proc 'msg
  | Receive 'proc 'proc 'msg
  | Timeout 'proc
  | Restart 'proc

datatype ('s, 'proc, 'msg) sendBuffer = Buffer 's "('proc \<times> 'msg) set"

(* --- KME --- *)
datatype ('status, 'id, 'key) kmeState = Default 'status "('id \<times> 'key) set"

fun kme_step where
  \<open>kme_step (Default s ks) (Receive sender _ (GetStatus _)) = (Default s ks, {(sender, Status s)})\<close> |
  \<open>kme_step (Default s ks) (Receive sender _ (GetKey _)) = (Default s ks, {(sender, Key ks)})\<close> |
  \<open>kme_step state _ = (state, {})\<close>

definition kme_trans where
"kme_trans pid =
  {(Buffer s msgs, a, Buffer s' (msgs \<union> ((\<lambda>msg. (pid, msg)) ` sent))) | s a s' msgs sent. kme_step s a = (s', sent) \<and> (\<exists>s m. a = Receive s pid m \<or> a = Timeout pid \<or> a = Restart pid)}
  \<union> {(Buffer s msgs, Send pid rcpt msg, Buffer s (msgs - {(pid,rcpt,msg)})) | s msgs rcpt msg. (pid,rcpt,msg) \<in> msgs}"

definition kme_asig where
"kme_asig pid =
 ({Receive s pid m | s m. True} \<union> {Timeout pid, Restart pid},
  {Send pid r m | r m. True},
  {})"

definition Kme where
"Kme pid s ks = (kme_asig pid, {Buffer (Default s ks) {}}, kme_trans pid, {}, {})"

lemma
  shows "IOA (Kme pid s ks)"
  unfolding IOA_def apply auto
  subgoal
    unfolding is_asig_of_def is_asig_def asig_projections asig_of_def Kme_def kme_asig_def by auto
  subgoal
    unfolding is_starts_of_def starts_of_def Kme_def kme_asig_def by auto
  subgoal
    unfolding is_trans_of_def trans_of_def Kme_def kme_trans_def 
      actions_def asig_of_def kme_asig_def asig_projections by auto
  subgoal
    unfolding input_enabled_def asig_projections asig_of_def kme_asig_def Kme_def trans_of_def kme_trans_def apply auto
       apply (metis sendBuffer.exhaust)
      apply (metis sendBuffer.exhaust)
    by (metis sendBuffer.exhaust surj_pair)+
  done

(* --- SAE --- *)
datatype 'proc saeState = Idle | CheckState 'proc | RequestingKey 'proc | RequestingKeyWithId

fun sae_step where
  \<open>sae_step kmeId Idle (Start _ targetSae) = (CheckState targetSae, {(kmeId, GetStatus targetSae)})\<close> |
  \<open>sae_step kmeId Idle (Receive sender _ (KeyId ids)) = (RequestingKeyWithId, {(kmeId, GetKeyWithId ids)})\<close> |
  \<open>sae_step kmeId (CheckState targetSae) (Receive sender _ (Status _)) = (RequestingKey targetSae, {(kmeId, GetKey targetSae)})\<close> |
  \<open>sae_step kmeId (RequestingKey targetSae) (Receive _ _ (Key ks)) = (Idle, {(targetSae, KeyId {fst idKey | idKey. idKey \<in> ks})})\<close> |
  \<open>sae_step _ state _ = (state, {})\<close>

definition sae_trans where
"sae_trans pid kmeId =
  {(Buffer s msgs, a, Buffer s' (msgs \<union> ((\<lambda>msg. (pid, msg)) ` sent))) | s a s' msgs sent. sae_step kmeId s a = (s', sent) \<and> (\<exists>s k m. a = Start pid k \<or> a = Receive s pid m \<or> a = Timeout pid \<or> a = Restart pid)}
  \<union> {(Buffer s msgs, Send pid rcpt msg, Buffer s (msgs - {(pid,rcpt,msg)})) | s msgs rcpt msg. (pid,rcpt,msg) \<in> msgs}"

definition sae_asig where
"sae_asig pid =
 ({Receive s pid m | s m. True} \<union> {Start pid targetSae | targetSae. True} \<union> {Timeout pid, Restart pid},
  {Send pid r m | r m. True},
  {})"

definition Sae where
"Sae pid kmeId = (sae_asig pid, {Buffer Idle {}}, sae_trans pid kmeId, {}, {})"

lemma
  shows "IOA (Sae pid kmeId)"
  unfolding IOA_def apply auto
  subgoal
    unfolding is_asig_of_def is_asig_def asig_projections asig_of_def Sae_def sae_asig_def by auto
  subgoal
    unfolding is_starts_of_def starts_of_def Sae_def sae_asig_def by auto
  subgoal
    unfolding is_trans_of_def trans_of_def Sae_def sae_trans_def 
      actions_def asig_of_def sae_asig_def asig_projections by auto
  subgoal
    unfolding input_enabled_def asig_projections asig_of_def sae_asig_def Sae_def trans_of_def sae_trans_def apply auto
       apply (metis sendBuffer.exhaust)
      apply (metis sendBuffer.exhaust)
    by (metis sendBuffer.exhaust surj_pair)+
  done

(* --- Channel --- *)
type_synonym ('proc, 'status, 'key, 'id) chan_state = "('proc \<times> 'proc \<times> ('proc, 'status, 'key, 'id) msg) set"

definition chan_trans where
"chan_trans =
  {(M, Send s r m, M \<union> {(s,r,m)}) | M s r m. True}
  \<union> {(M, Receive s r m, M) | M s r m. (s,r,m) \<in> M}"

definition chan_asig :: "('proc,'t) action signature" where
"chan_asig =
 ({Send s r m | s r m. True},
  {Receive s r m | s r m. True},
  {})"

definition Channel :: "(('proc,('proc, 'status, 'key, 'id) msg) action, ('proc, 'status, 'key, 'id) chan_state) ioa" where
"Channel = (chan_asig, { {} }, chan_trans, {}, {})"

lemma
  shows "IOA (Channel)"
  unfolding IOA_def apply auto
  subgoal
    unfolding is_asig_of_def is_asig_def asig_projections asig_of_def Channel_def chan_trans_def chan_asig_def by auto
  subgoal
    unfolding is_starts_of_def starts_of_def Channel_def chan_asig_def by auto
  subgoal
    unfolding is_trans_of_def trans_of_def Channel_def chan_trans_def 
      actions_def asig_of_def chan_asig_def asig_projections by auto
  subgoal
    unfolding input_enabled_def asig_projections asig_of_def Channel_def chan_asig_def trans_of_def chan_trans_def by auto
  done

lemma 1:
  assumes "IOA A \<and> IOA B"
    and "compatible A B"
  shows "is_asig_of (A \<parallel> B)"
  using assms 
  unfolding compatible_def is_asig_of_def is_asig_def asig_projections asig_of_def par_def asig_comp_def apply auto
  unfolding IOA_def is_asig_of_def asig_of_def is_asig_def asig_projections actions_def by auto

lemma 2:
  assumes "IOA A \<and> IOA B"
    and "compatible A B"
  shows "is_starts_of (A \<parallel> B)"
  using assms(1)
  unfolding is_starts_of_def starts_of_def par_def asig_comp_def apply simp
  unfolding IOA_def is_starts_of_def starts_of_def by auto

lemma 3:
  assumes "IOA A \<and> IOA B"
    and "compatible A B"
  shows "is_trans_of (A \<parallel> B)"
  using assms(1) is_trans_of_par by metis

lemma 4:
  assumes "IOA A \<and> IOA B"
    and "compatible A B"
  shows "input_enabled (A \<parallel> B)"
  unfolding input_enabled_def
proof (clarify)
  fix a s1l s1r
  assume asm:"a \<in> inp (A \<parallel> B)"
  then have inp:"a \<in> (inputs (asig_of A) \<union> inputs (asig_of B)) - (outputs (asig_of A) \<union> outputs (asig_of B))"
    unfolding asig_inputs_def par_def asig_comp_def asig_of_def by simp
  have "trans_of (A \<parallel> B) = {tr.
        let
          s = fst tr;
          a = fst (snd tr);
          t = snd (snd tr)
        in
          (a \<in> act A \<or> a \<in> act B) \<and>
          (if a \<in> act A then (fst s, a, fst t) \<in> trans_of A
           else fst t = fst s) \<and>
          (if a \<in> act B then (snd s, a, snd t) \<in> trans_of B
           else snd t = snd s)}"
    unfolding par_def trans_of_def by simp
  then have trans:"trans_of (A \<parallel> B) = {(s, a, s') | s a s'. (a \<in> act A \<or> a \<in> act B) \<and>
          (if a \<in> act A then (fst s, a, fst s') \<in> trans_of A
           else fst s' = fst s) \<and>
          (if a \<in> act B then (snd s, a, snd s') \<in> trans_of B
           else snd s' = snd s)}"
    using Collect_cong by fastforce
  \<comment> \<open>Step 1: Obtain the next state for A (it either steps or stutters)\<close>
  have step_A: "\<exists>s2l. if a \<in> act A then (s1l, a, s2l) \<in> trans_of A else s2l = s1l"
  proof (cases "a \<in> act A")
    case True
    \<comment> \<open>Since a is an input of the composite and an action of A, it must be an input of A.\<close>
    have "a \<in> inputs (asig_of A)"
      using True inp unfolding actions_def asig_inputs_def asig_outputs_def asig_internals_def asig_projections
      by (metis Diff_iff True Un_iff asig_inputs_def asig_outputs_def assms(2) compat_commute inpAAactB_is_inpBoroutB)
    \<comment> \<open>Because A is an IOA, it is input enabled, so a valid transition exists.\<close>
    then obtain s2l where "(s1l, a, s2l) \<in> trans_of A"
      using assms(1) unfolding IOA_def input_enabled_def by fast
    then show ?thesis using True by auto
  next
    case False
    \<comment> \<open>If it's not an action of A, A just stutters.\<close>
    then show ?thesis by simp
  qed
  \<comment> \<open>Step 2: Obtain the next state for B (it either steps or stutters)\<close>
  have step_B: "\<exists>s2r. if a \<in> act B then (s1r, a, s2r) \<in> trans_of B else s2r = s1r"
  proof (cases "a \<in> act B")
    case True
    have "a \<in> inputs (asig_of B)"
      using True inp unfolding actions_def asig_inputs_def asig_outputs_def asig_internals_def asig_projections
      by (metis Diff_iff True Un_iff asig_inputs_def asig_outputs_def assms(2) inpAAactB_is_inpBoroutB)
    then obtain s2r where "(s1r, a, s2r) \<in> trans_of B"
      using assms(1) unfolding IOA_def input_enabled_def by blast
    then show ?thesis using True by auto
  next
    case False
    then show ?thesis by simp
  qed
  \<comment> \<open>Step 3: Extract the specific states from our helper lemmas\<close>
  from step_A obtain s2l where s2l_def: "if a \<in> act A then (s1l, a, s2l) \<in> trans_of A else s2l = s1l" by blast
  from step_B obtain s2r where s2r_def: "if a \<in> act B then (s1r, a, s2r) \<in> trans_of B else s2r = s1r" by blast
  \<comment> \<open>Step 4: Prove that the action MUST belong to at least one of the automata\<close>
  have "a \<in> act A \<or> a \<in> act B"
    using inp unfolding actions_def asig_inputs_def asig_of_def asig_projections by auto
  \<comment> \<open>Step 5: Combine them into the final composite transition\<close>
  then have "((s1l, s1r), a, (s2l, s2r)) \<in> trans_of (A \<parallel> B)"
    unfolding trans using s2l_def s2r_def by simp
  then show "\<exists>s2. ((s1l, s1r), a, s2) \<in> trans_of (A \<parallel> B)"
    by fast
qed

lemma
  assumes "IOA A \<and> IOA B"
    and "compatible A B"
  shows "IOA (A \<parallel> B)"
  unfolding IOA_def using 1 2 3 4 assms by metis
  
  

end