theory Kleppmann_inv_1
  imports Kleppmann_inv_def Kleppmann_step_inducts
begin

lemma invariant1_coordinator:
  assumes "coordinator_step 0 (states 0) event = (new_state, sent)"
    and "msgs' = msgs ∪ ((λmsg. (0, msg)) ` sent)"
    and "states' = states (0 := new_state)"
    and "execute tupac_step (λp. Initial (init_val p) UNIV r) UNIV (events @ [(0, event)]) msgs' states'"
    and "inv1 msgs states"
  shows "inv1 msgs' states'"
  using assms apply (induction rule: coordinator_induct)
  using inv1_def UnCI assms(2,3,5) apply (metis (mono_tags, lifting) fun_upd_apply)+
  done

lemma invariant1_participant:
  assumes "participant_step (states proc) event = (new_state, sent)"
    and "proc ≠ 0"
    and "msgs' = msgs ∪ ((λmsg. (proc, msg)) ` sent)"
    and "states' = states (proc := new_state)"
    and "execute tupac_step (λp. Initial (init_val p) UNIV r) UNIV (events @ [(proc, event)]) msgs' states'"
    and "inv1 msgs states"
  shows "inv1 msgs' states'"
  using assms
proof (induction rule: participant_induct)
  case (Init_Prep_Yes t a r sender t')
  then have "∃proc a ack'. (proc ≠ 0 ∧ states proc = Committed a ack') ⟷ (proc ≠ 0 ∧ states' proc = Committed a ack')"
    using assms(4) by metis
  moreover have "∃sender rcpt. ((sender, Send rcpt Commit) ∈ msgs) ⟷ ((sender, Send rcpt Commit) ∈ msgs')"
    using assms(3) Init_Prep_Yes(5) by simp
  ultimately show ?case
    by (metis (no_types, lifting) Init_Prep_Yes(4) UnCI assms(3,4,6) fun_upd_apply inv1_def
        state.distinct(19))
next
  case (Init_Prep_No t a r sender t')
  then have "∃proc a ack'. (proc ≠ 0 ∧ states proc = Committed a ack') ⟷ (proc ≠ 0 ∧ states' proc = Committed a ack')"
    using assms(4) by metis
  moreover have "∃sender rcpt. ((sender, Send rcpt Commit) ∈ msgs) ⟷ ((sender, Send rcpt Commit) ∈ msgs')"
    using assms(3) Init_Prep_No(5) by simp
  ultimately show ?case
    by (metis (no_types, lifting) Init_Prep_No(4) UnCI assms(3,4,6) fun_upd_apply inv1_def
        state.distinct(25))
next
  case (Init_Timeout t a r)
  then have "∃proc a ack'. (proc ≠ 0 ∧ states proc = Committed a ack') ⟷ (proc ≠ 0 ∧ states' proc = Committed a ack')"
    using assms(4) by metis
  moreover have "∃sender rcpt. ((sender, Send rcpt Commit) ∈ msgs) ⟷ ((sender, Send rcpt Commit) ∈ msgs')"
    using assms(3) Init_Timeout(4) by simp
  ultimately show ?case
    by (metis (no_types, lifting) Init_Timeout(3) UnCI assms(3,4,6) fun_upd_apply inv1_def
        state.distinct(25))
next
  case (Prep_Commit sender)
  then have "∃sender rcpt. (sender, Send rcpt Commit) ∈ msgs"
    using assms(3,5) execute_receive Un_commute image_insert image_is_empty by (smt (verit, ccfv_SIG) 
          insert_iff insert_is_Un msg.distinct(27) prod.inject send.inject)
  then have "∃sender rcpt. (sender, Send rcpt Commit) ∈ msgs'"
    using assms(3) by auto
  then show ?case
    using inv1_def by blast
next
  case (Prep_Abort sender)
  then have "∃proc a ack'. (proc ≠ 0 ∧ states proc = Committed a ack') ⟷ (proc ≠ 0 ∧ states' proc = Committed a ack')"
    using assms(4) by metis
  moreover have "∃sender rcpt. ((sender, Send rcpt Commit) ∈ msgs) ⟷ ((sender, Send rcpt Commit) ∈ msgs')"
    using assms(3) Prep_Abort(4) by simp
  ultimately show ?case
    by (metis (no_types, lifting) Prep_Abort(3) UnCI assms(3,4,6) fun_upd_apply inv1_def
        state.distinct(25))
next
  case (Committed_Commit all ack sender)
  then have "∃sender rcpt. (sender, Send rcpt Commit) ∈ msgs"
    using assms(3,5) execute_receive Un_commute image_insert image_is_empty by (smt (verit, ccfv_SIG) 
          insert_iff insert_is_Un msg.distinct(27) prod.inject send.inject)
  then have "∃sender rcpt. (sender, Send rcpt Commit) ∈ msgs'"
    using assms(3) by auto
  then show ?case
    using inv1_def by blast
next
  case (Aborted_Abort all ack sender)
  then have "∃proc a ack'. (proc ≠ 0 ∧ states proc = Committed a ack') ⟷ (proc ≠ 0 ∧ states' proc = Committed a ack')"
    using assms(4) by metis
  moreover have "∃sender rcpt. ((sender, Send rcpt Commit) ∈ msgs) ⟷ ((sender, Send rcpt Commit) ∈ msgs')"
    using assms(3) Aborted_Abort(4) by simp
  ultimately show ?case
    by (metis (no_types, lifting) UnCI assms(3,4,6) fun_upd_apply inv1_def
        Aborted_Abort(3) state.distinct(25))
qed

lemma invariant1:
  assumes ‹execute tupac_step (λp. Initial (init_val p) UNIV r) UNIV events msgs' states'›
  shows "inv1 msgs' states'"
  using assms proof(induction events arbitrary: msgs' states' r rule: List.rev_induct)
  case Nil
  then have statesInit:"∀p. states' p = Initial (init_val p) UNIV r"
    using execute_init assms by fast
  moreover have msgsEmpty:"msgs' = {}"
    using execute_init Nil by fast
  ultimately show ?case
    using inv1_def by auto
next
  case (snoc x events)
  obtain proc event where "x = (proc, event)"
    by fastforce
  hence exec: "execute tupac_step (λp. Initial (init_val p) UNIV r) UNIV
               (events @ [(proc, event)]) msgs' states'"
    using snoc.prems assms by fast
  from this obtain msgs states sent new_state
    where step_rel1: "execute tupac_step (λp. Initial (init_val p) UNIV r) UNIV events msgs states"
      and step_rel2: "tupac_step proc (states proc) event = (new_state, sent)"
      and step_rel3: "msgs' = msgs ∪ ((λmsg. (proc, msg)) ` sent)"
      and step_rel4: "states' = states (proc := new_state)"
    by auto
  show ?case
  proof (cases "proc = 0")
    case True
    then have "coordinator_step proc (states 0) event = (new_state, sent)"
      using step_rel2 by simp
    moreover have"inv1 msgs states"
      using snoc.IH step_rel1 by fast
    ultimately show ?thesis
      using invariant1_coordinator True step_rel3 step_rel4 exec by metis
  next
    case False
    then have "participant_step (states proc) event = (new_state, sent)"
      using step_rel2 by simp
    moreover have"inv1 msgs states"
      using snoc.IH step_rel1 by fast
    ultimately show ?thesis
      using invariant1_participant False step_rel3 step_rel4 exec by metis
  qed
qed

end