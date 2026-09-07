theory Automata_2PC
  imports Automata
begin

(* --- Datatypes --- *)
datatype 't msg = Prepare (transaction: 't) | Yes | No | Commit | Abort | Ack

datatype ('proc, 'msg) action = 
    Start "'proc" 
  | Send "'proc" "'proc" "'msg" 
  | Receive "'proc" "'proc" "'msg" 
  | Timeout "'proc" 
  | Restart "'proc"


(* --- Coordinator --- *)
datatype ('t,'proc) cstate = CInitial (transaction: 't) (all: "'proc set") (retry_count:"nat") 
  | Collecting (transaction: 't) (all: "'proc set") (yes:"'proc set") (retry_count:"nat") 
  | CCommitted (all: "'proc set") (ack: "'proc set") 
  | CAborted (all: "'proc set") (ack: "'proc set") 
  | Forgotten
datatype ('t,'proc) coord_state = CState "('t,'proc) cstate" "('proc × 'proc × 't msg) set"

fun coordinator_step:: 
    "'proc ⇒ ('t, 'proc) cstate ⇒ ('proc, 't msg) action ⇒ ('t, 'proc) cstate × ('proc × 't msg) set"  where
  ‹coordinator_step pid (CInitial t a r) (Start _) = (Collecting t a {pid} r, {(q, (Prepare t)) | q. q ∈ a - {pid}})› |
  ‹coordinator_step pid (Collecting t a y r) (Receive sender _ msg) = 
      (case msg of
        Yes ⇒(if y ∪ {sender} = a then (CCommitted a {pid}, {(q, Commit) | q. q ∈ a - {pid}}) else (Collecting t a (y ∪ {sender}) r, {})) |
        No ⇒(CAborted a {pid}, {(q, Abort) | q. q ∈ a - {pid}}) |
        _ ⇒(Collecting t a y r, {}))› |
  ‹coordinator_step pid (Collecting t a y 0) (Timeout _) = (CAborted a {pid}, {(q, Abort) | q. q ∈ a - {pid}})› |
  ‹coordinator_step pid (Collecting t a y (Suc r)) (Timeout _) = (Collecting t a y r, {(q, Prepare t) | q. q ∈ (a - y)})› |
  ‹coordinator_step pid (CCommitted a ack') (Receive sender _ Ack) = 
      (if {sender} ∪ ack' = a then (Forgotten, {}) else (CCommitted a (ack' ∪ {sender}), {}))› |
  ‹coordinator_step pid (CCommitted a ack') (Timeout _) = (CCommitted a ack', {(q, Commit) | q. q ∈ (a - ack')})› |
  ‹coordinator_step pid (CCommitted a ack') (Restart _) = (CCommitted a ack', {(q, Commit) | q. q ∈ a - {pid}})› |
  ‹coordinator_step pid (CAborted a ack') (Receive sender _ Ack) = 
      (if {sender} ∪ ack' = a then (Forgotten, {}) else (CAborted a (ack' ∪ {sender}), {}))› |
  ‹coordinator_step pid (CAborted a ack') (Timeout _) = (CAborted a ack', {(q, Abort) | q. q ∈ (a - ack')})› |
  ‹coordinator_step pid (CAborted a ack') (Restart _) = (CAborted a ack', {(q, Abort) | q. q ∈ a - {pid}})› |
  ‹coordinator_step _ state _ = (state, {})›

definition coord_trans :: 
  "'proc ⇒ (('t,'proc) coord_state × ('proc,'t msg) action × ('t,'proc) coord_state) set" where
"coord_trans pid =
  {(CState s msgs, a, CState s' (msgs ∪ ((λmsg. (pid, msg)) ` sent))) | s a s' msgs sent. coordinator_step pid s a = (s', sent) ∧ (∃s m. a = Start pid ∨ a = Receive s pid m ∨ a = Timeout pid ∨ a = Restart pid)}
  ∪ {(CState s msgs, Send pid rcpt msg, CState s (msgs - {(pid,rcpt,msg)})) | s msgs rcpt msg. (pid,rcpt,msg) ∈ msgs}"

definition coord_asig :: "'proc ⇒ ('proc,'t) action signature" where
"coord_asig pid =
 ({Receive q pid m | q m. True} ∪ {Start pid, Timeout pid, Restart pid},
  {Send pid q m | q m. True},
  {})"

definition Coordinator :: "'p ⇒ 't ⇒ 'p set ⇒ nat ⇒ (('p,'t msg) action, ('t,'p) coord_state) ioa" where
"Coordinator pid t a r = (coord_asig pid, {CState (CInitial t a r) {}}, coord_trans pid, {}, {})"


(* --- Participant --- *)
datatype 't pstate = PInitial (transaction: 't)
  | Prepared 
  | PCommitted
  | PAborted
datatype ('t,'proc) part_state = PState "'t pstate" "('proc × 'proc × 't msg) set"

fun participant_step::
    "'proc ⇒ 't pstate ⇒ ('proc, 't msg) action ⇒ 't pstate × ('proc × 't msg) set"  where
  ‹participant_step pid (PInitial t) (Receive sender _ (Prepare t')) = 
      (if t = t' then (Prepared, {(sender, Yes)}) else (PAborted, {(sender, No)}))› |
  ‹participant_step pid (PInitial t) (Timeout p) = (PAborted, {})› |
  ‹participant_step pid Prepared (Receive sender rcpt msg) = 
      (case msg of
        Commit ⇒ (PCommitted, {(sender, Ack)}) |
        Abort ⇒ (PAborted, {(sender, Ack)}) |
        _ ⇒ (Prepared, {}))› |
  ‹participant_step pid PCommitted (Receive sender rcpt Commit) = (PCommitted, {(sender, Ack)})› |
  ‹participant_step pid PAborted (Receive sender rcpt Abort) = (PAborted, {(sender, Ack)})› |
  ‹participant_step _ state _ = (state, {})›

definition part_trans :: 
  "'proc ⇒ (('t,'proc) part_state × ('proc,'t msg) action × ('t,'proc) part_state) set" where
"part_trans pid =
  {(PState s msgs, a, PState s' (msgs ∪ ((λmsg. (pid, msg)) ` sent))) | s a s' msgs sent. participant_step pid s a = (s', sent) ∧ (∃s m. a = Receive s pid m ∨ a = Timeout pid ∨ a = Restart pid)}
  ∪ {(PState s msgs, Send pid rcpt msg, PState s (msgs - {(pid,rcpt,msg)})) | s msgs rcpt msg. (pid,rcpt,msg) ∈ msgs}"


(* --- Participants collection --- *)
definition parts_asig :: "'proc set ⇒ ('proc,'t msg) action signature" where
"parts_asig P = 
 ({Receive q p m | q p m. p ∈ P} ∪ {Timeout p | p. p ∈ P} ∪ {Restart p | p. p ∈ P}, 
  {Send p q m | p q m. p ∈ P}, 
  {})"

definition parts_trans :: "'proc set ⇒ (('proc ⇒ ('t,'proc) part_state) × ('proc,'t msg) action × ('proc ⇒ ('t,'proc) part_state)) set" where
"parts_trans P = { (s, a, s'). 
    ∀p. if p ∈ P ∧ ((∃q m. a = Receive q p m) ∨ a = Timeout p ∨ a = Restart p ∨ (∃q m. a = Send p q m))
        then (s p, a, s' p) ∈ part_trans p
        else s' p = s p }"

definition Participants :: "'proc set ⇒ ('proc ⇒ 't) ⇒ (('proc,'t msg) action, 'proc ⇒ ('t,'proc) part_state) ioa" where
"Participants P t = (parts_asig P, {λp. PState (PInitial (t p)) {}}, parts_trans P, {}, {})"


(* --- Channel --- *)
type_synonym ('proc,'t) chan_state = "('proc × 'proc × 't msg) set"

definition chan_trans :: "(('proc,'t) chan_state × ('proc,'t msg) action × ('proc,'t) chan_state) set" where
"chan_trans =
  {(M, Send s r m, M ∪ {(s,r,m)}) | M s r m. True}
  ∪ {(M, Receive s r m, M) | M s r m. (s,r,m) ∈ M}"

definition chan_asig :: "('proc,'t) action signature" where
"chan_asig =
 ({Send s r m | s r m. True},
  {Receive s r m | s r m. True},
  {})"

definition Channel :: "(('proc,'t msg) action, ('proc,'t) chan_state) ioa" where
"Channel = (chan_asig, { {} }, chan_trans, {}, {})"


(* --- System Composition & Properties --- *)
definition System  where
"System t P r = ((Coordinator 0 (t 0) (P ∪ {0}) r ∥ Channel) ∥ Participants P t)"

(* --- Helpers ---*)
lemma par_trans_unfold:
  assumes "((sa,sb),a,(sa',sb')) ∈ trans_of (A ∥ B)"
  shows "((sa,a,sa') ∈ trans_of A ∨ sa = sa') ∧
         ((sb,a,sb') ∈ trans_of B ∨ sb = sb')"
  using assms unfolding trans_of_def par_def apply auto
   apply (metis comp_eq_dest_lhs fstI)
  apply(metis comp_eq_dest_lhs sndI)
  done

lemma System_trans_unfold:
  assumes "(((c, ch), p), a, ((c', ch'), p')) ∈ trans_of (System t P r)"
  shows "((c, a, c') ∈ coord_trans 0 ∨ c = c') ∧
         ((ch, a, ch') ∈ chan_trans ∨ ch = ch') ∧
         ((p, a, p') ∈ parts_trans P ∨ p = p')"
proof -
  obtain Co where Co_def:"Co = Coordinator 0 (t 0) (P ∪ {0}) r"
    by simp
  moreover obtain Ps where Ps_def:"Ps = Participants P t"
    by simp
  ultimately have "(((c,ch), a, (c',ch')) ∈ trans_of (Co ∥ Channel) ∨ (c, ch) = (c', ch')) ∧
                  ((p, a, p') ∈ trans_of Ps ∨ p = p')"
    using par_trans_unfold assms by (metis System_def)
  moreover have "trans_of Co = coord_trans 0 ∧ trans_of Channel = chan_trans ∧ trans_of Ps = parts_trans P"
    unfolding Co_def Ps_def trans_of_def Coordinator_def Channel_def Participants_def by simp
  ultimately show ?thesis
    using par_trans_unfold by fast
qed

lemma System_trans_inv [elim]:
  assumes "(((c, ch), p), a, ((c', ch'), p')) ∈ trans_of (System t P r)"
  obtains (System_Step)
    "((c, a, c') ∈ coord_trans 0 ∨ c = c')"
    "((ch, a, ch') ∈ chan_trans ∨ ch = ch')"
    "((p, a, p') ∈ parts_trans P ∨ p = p')"
  using assms System_trans_unfold by metis

(*Nich benötigt*)
lemma coord_trans_inv [elim]:
  assumes "(CState c msgs, a, CState c' msgs') ∈ coord_trans pid"
  obtains 
    (Step) sent where "coordinator_step pid c a = (c', sent)" 
                      "msgs' = msgs ∪ ((λmsg. (pid, msg)) ` sent)"
                      "(∃s r m. a = Start r ∨ a = Receive s r m ∨ a = Timeout r ∨ a = Restart r)"
  | (Send) rcpt msg where "a = Send pid rcpt msg" 
                          "c' = c" 
                          "msgs' = msgs - {(pid, rcpt, msg)}" 
                          "(pid, rcpt, msg) ∈ msgs"
  using assms unfolding coord_trans_def by auto

lemma part_trans_inv [elim]:
  assumes "(PState s msgs, a, PState s' msgs') ∈ part_trans pid"
  obtains 
    (Step) sent where "participant_step pid s a = (s', sent)" 
                      "msgs' = msgs ∪ ((λmsg. (pid, msg)) ` sent)"
                      "(∃s r m. a = Receive s r m ∨ a = Timeout r ∨ a = Restart r)"
  | (Send) rcpt msg where "a = Send pid rcpt msg" 
                          "s' = s" 
                          "msgs' = msgs - {(pid, rcpt, msg)}" 
                          "(pid, rcpt, msg) ∈ msgs"
  using assms unfolding part_trans_def by auto

lemma chan_trans_inv [elim]:
  assumes "(M, a, M') ∈ chan_trans"
  obtains 
    (Send) s r m where "a = Send s r m" "M' = M ∪ {(s, r, m)}"
  | (Receive) s r m where "a = Receive s r m" "M' = M" "(s, r, m) ∈ M"
  using assms unfolding chan_trans_def by auto

lemma participant_step_inv [consumes 1, case_names 
    Init_Prep_Yes Init_Prep_No Init_Timeout 
    Prep_Commit Prep_Abort 
    Committed_Commit Aborted_Abort Stutter]:
  assumes "participant_step pid s a = (s', sent)"
  obtains 
    (Init_Prep_Yes) t sender where "s = PInitial t" "∃p. a = Receive sender p (Prepare t)" "s' = Prepared" "sent = {(sender, Yes)}"
  | (Init_Prep_No) t t' sender where "s = PInitial t" "∃p. a = Receive sender p (Prepare t')" "t ≠ t'" "s' = PAborted" "sent = {(sender, No)}"
  | (Init_Timeout) t where "s = PInitial t" "∃p. a = Timeout p" "s' = PAborted" "sent = {}"
  | (Prep_Commit) sender where "s = Prepared" "∃p. a = Receive sender p Commit" "s' = PCommitted" "sent = {(sender, Ack)}"
  | (Prep_Abort) sender where "s = Prepared" "∃p. a = Receive sender p Abort" "s' = PAborted" "sent = {(sender, Ack)}"
  | (Committed_Commit) sender where "s = PCommitted" "∃p. a = Receive sender p Commit" "s' = PCommitted" "sent = {(sender, Ack)}"
  | (Aborted_Abort) sender where "s = PAborted" "∃p. a = Receive sender p Abort" "s' = PAborted" "sent = {(sender, Ack)}"
  | (Stutter) "s' = s" "sent = {}"
  using assms
  by (cases "(pid, s, a)" rule: participant_step.cases) 
     (auto split: if_splits msg.splits action.splits pstate.splits)

(*Nich benötigt*)
lemma coordinator_step_inv [consumes 1, case_names 
    Init_Start 
    Collect_Yes_Commit Collect_Yes_Wait Collect_No Collect_Timeout_Abort Collect_Timeout_Retry
    Commit_Ack_Done Commit_Ack_Wait Commit_Timeout Commit_Restart
    Abort_Ack_Done Abort_Ack_Wait Abort_Timeout Abort_Restart
    Stutter]:
  assumes "coordinator_step pid s a = (s', sent)"
  obtains
    (Init_Start) t A r where "s = CInitial t A r" "∃p. a = Start p" "s' = Collecting t A {pid} r" "sent = {(q, Prepare t) | q. q ∈ A - {pid}}"
  | (Collect_Yes_Commit) t A y r sender where "s = Collecting t A y r" "∃p. a = Receive sender p Yes" "y ∪ {sender} = A" "s' = CCommitted A {pid}" "sent = {(q, Commit) | q. q ∈ A - {pid}}"
  | (Collect_Yes_Wait) t A y r sender where "s = Collecting t A y r" "∃p. a = Receive sender p Yes" "y ∪ {sender} ≠ A" "s' = Collecting t A (y ∪ {sender}) r" "sent = {}"
  | (Collect_No) t A y r sender where "s = Collecting t A y r" "∃p. a = Receive sender p No" "s' = CAborted A {pid}" "sent = {(q, Abort) | q. q ∈ A - {pid}}"
  | (Collect_Timeout_Abort) t A y where "s = Collecting t A y 0" "∃p. a = Timeout p" "s' = CAborted A {pid}" "sent = {(q, Abort) | q. q ∈ A - {pid}}"
  | (Collect_Timeout_Retry) t A y r where "s = Collecting t A y (Suc r)" "∃p. a = Timeout p" "s' = Collecting t A y r" "sent = {(q, Prepare t) |q. q ∈ (A - y)}"
  | (Commit_Ack_Done) A ack' sender where "s = CCommitted A ack'" "∃p. a = Receive sender p Ack" "{sender} ∪ ack' = A" "s' = Forgotten" "sent = {}"
  | (Commit_Ack_Wait) A ack' sender where "s = CCommitted A ack'" "∃p. a = Receive sender p Ack" "{sender} ∪ ack' ≠ A" "s' = CCommitted A (ack' ∪ {sender})" "sent = {}"
  | (Commit_Timeout) A ack' where "s = CCommitted A ack'" "∃p. a = Timeout p" "s' = CCommitted A ack'" "sent = {(q, Commit) | q. q ∈ (A - ack')}"
  | (Commit_Restart) A ack' where "s = CCommitted A ack'" "∃p. a = Restart p" "s' = CCommitted A ack'" "sent = {(q, Commit) | q. q ∈ A - {pid}}"
  | (Abort_Ack_Done) A ack' sender where "s = CAborted A ack'" "∃p. a = Receive sender p Ack" "{sender} ∪ ack' = A" "s' = Forgotten" "sent = {}"
  | (Abort_Ack_Wait) A ack' sender where "s = CAborted A ack'" "∃p. a = Receive sender p Ack" "{sender} ∪ ack' ≠ A" "s' = CAborted A (ack' ∪ {sender})" "sent = {}"
  | (Abort_Timeout) A ack' where "s = CAborted A ack'" "∃p. a = Timeout p" "s' = CAborted A ack'" "sent = {(q, Abort) | q. q ∈ (A - ack')}"
  | (Abort_Restart) A ack' where "s = CAborted A ack'" "∃p. a = Restart p" "s' = CAborted A ack'" "sent = {(q, Abort) | q. q ∈ A - {pid}}"
  | (Stutter) "s' = s" "sent = {}"
  using assms
  by (cases "(pid, s, a)" rule: coordinator_step.cases)
     (auto split: if_splits msg.splits action.splits cstate.splits)

end