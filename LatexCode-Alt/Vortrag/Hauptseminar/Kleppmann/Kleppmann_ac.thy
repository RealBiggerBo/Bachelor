theory Kleppmann_ac
  imports Kleppmann_inv_1 
          Kleppmann_inv_3 
          Kleppmann_inv_procs 
          Kleppmann_inv_111 
          Kleppmann_inv_212223
          Kleppmann_inv_41
begin

theorem ac1_NoCoordinator:
  assumes ‹execute tupac_step (λp. Initial (init_val p) UNIV r) UNIV events msgs states›
    and ‹proc1 ≠ 0 ∧ proc2 ≠ 0›
    and ‹states proc1 = Committed a b ∨ states proc1 = Aborted a b› 
    and ‹states proc2 = Committed c d ∨ states proc2 = Aborted c d›
  shows ‹states proc1 = Committed a b ⟷ states proc2 = Committed c d›
proof (rule ccontr)
  assume asm1:"¬(states proc1 = Committed a b ⟷ states proc2 = Committed c d)"
  have inv:"inv1 msgs states ∧ inv3 msgs states ∧ inv11 msgs states UNIV ∧ inv17 msgs states"
    using invariants123 invariant1 invariant3 assms(1) by blast
  then show "False"
  proof(cases "states proc1 = Committed a b")
    case True
    then have proc2Abort:"states proc2 = Aborted c d"
      using asm1 assms(4) by auto
    then have commitMsg:"(∃sender rcpt. (sender, Send rcpt Commit) ∈ msgs)"
      using True inv by (metis assms(2) inv1_def)
    then have noAbort:"(∀sender recpt. (sender, Send recpt Abort) ∉ msgs)"
      using inv inv3_def by metis
    then have "(∀p ∈ UNIV. p ≠ 0 ⟶ (∃rcpt. (p, Send rcpt Yes) ∈ msgs))"
      using inv inv11_def by (metis commitMsg)
    then have "∃rcpt. (proc2, Send rcpt Yes) ∈ msgs"
      using assms(2) by auto
    moreover have "∀rcpt. (proc2, Send rcpt Yes) ∉ msgs"
      using proc2Abort assms(2) noAbort by (meson inv inv17_def)
    ultimately show ?thesis
      by simp
  next
    case False
    then have Aborted: "states proc1 = Aborted a b"
      using assms(3) by auto
    then have "states proc2 = Committed c d"
      using asm1 assms(4) by auto
    then have commitMsg:"(∃sender rcpt. (sender, Send rcpt Commit) ∈ msgs)"
      using inv by (metis assms(2) inv1_def)
    then have noAbort:"(∀sender recpt. (sender, Send recpt Abort) ∉ msgs)"
      using inv inv3_def by metis
    then have "(∀p ∈ UNIV. p ≠ 0 ⟶ (∃rcpt. (p, Send rcpt Yes) ∈ msgs))"
      using inv inv11_def by (metis commitMsg)
    then have "(∃rcpt. (proc1, Send rcpt Yes) ∈ msgs)"
      using assms(2) by simp
    moreover have "(∀rcpt. (proc1, Send rcpt Yes) ∉ msgs)"
      using Aborted assms(2) noAbort by (meson inv inv17_def)
    ultimately show ?thesis
      by simp
  qed
qed

theorem ac1_OneCoordinator:
  assumes ‹execute tupac_step (λp. Initial (init_val p) UNIV r) UNIV events msgs states›
    and ‹p ≠ 0›
    and ‹states 0 = Committed a b ∨ states 0 = Aborted a b› 
    and ‹states p = Committed c d ∨ states p = Aborted c d›
  shows ‹states 0 = Committed a b ⟷ states p = Committed c d›
proof
  assume asmCommitted:"states 0 = Committed a b"
  have inv:"inv11 msgs states UNIV ∧ inv17 msgs states ∧ inv15 msgs states"
    using invariants123 invariant15 assms(1) by blast
  show "states p = Committed c d"
  proof(rule ccontr)
    assume asmAborted: "states p ≠ Committed c d"
    then have proc2Abort:"states p = Aborted c d"
      using assms(4) by auto
    then have "(∀p ∈ UNIV. p ≠ 0 ⟶ (∃rcpt. (p, Send rcpt Yes) ∈ msgs))"
      using inv inv11_def by (metis asmCommitted)
    then have "∃rcpt. (p, Send rcpt Yes) ∈ msgs"
      using assms(2) by auto
    moreover have noAbort:"∀sender rcpt. (sender, Send rcpt Abort) ∉ msgs"
      using inv15_def asmCommitted inv by metis
    moreover have "∀rcpt. (p, Send rcpt Yes) ∉ msgs"
      using proc2Abort assms(2) noAbort by (meson inv inv17_def)
    ultimately show "False"
      by simp
    thm inv17_def
  qed
next
  assume asmCommitted:"states p = Committed c d"
  have inv:"inv1 msgs states ∧ inv111 msgs states"
    using invariants123 invariant1 invariant111 assms(1) invariant3 by blast
  have commitMsg:"(∃sender rcpt. (sender, Send rcpt Commit) ∈ msgs)"
    using inv asmCommitted inv1_def assms(2) by metis
  then have "∃all ack. states 0 = Committed all ack ∨ states 0 = Forgotten"
    using inv inv111_def by metis
  then show "states 0 = Committed a b"
    using assms(3) by force
qed

(*all processes that decide must decide on the same value*)
theorem ac1:
  assumes ‹execute tupac_step (λp. Initial (init_val p) UNIV r) UNIV events msgs states›
    and ‹states proc1 = Committed a b ∨ states proc1 = Aborted a b› 
    and ‹states proc2 = Committed c d ∨ states proc2 = Aborted c d›
  shows ‹states proc1 = Committed a b ⟷ states proc2 = Committed c d›
proof(cases "proc1 = proc2")
  case True
  then show ?thesis 
    using assms by auto
next
  case False
  then show ?thesis
  proof(cases "proc1 = 0 ∨ proc2 = 0")
    case True
    then show ?thesis
      using ac1_OneCoordinator by (metis assms(1-3) state.distinct(25))
  next
    case False
    then have "proc1 ≠ 0 ∧ proc2 ≠ 0"
      by satx
    then show ?thesis
      using ac1_NoCoordinator assms by blast
  qed
qed

(*once a process decides it cannot change its decision*)
theorem ac2:
  assumes ‹execute tupac_step (λp. Initial (init_val p) UNIV r) UNIV events msgs states›
    and step: ‹tupac_step proc (states proc) event = (new_state, sent)›
  shows ‹(∃a b. states proc = Committed a b) ⟶ 
        (∃c d. new_state = Committed c d) ∨ (proc = 0 ∧ new_state = Forgotten)›
    and ‹(∃a b. states proc = Aborted a b) ⟶ 
        (∃c d. new_state = Aborted c d) ∨ (proc = 0 ∧ new_state = Forgotten)›
    and ‹states proc = Forgotten ⟶ 
        (proc = 0 ∧ new_state = Forgotten)›
  using invariant212223 assms inv21_def apply metis
  using invariant212223 assms inv22_def apply metis
  using invariant212223 assms inv23_def apply metis
  done

(*commit only if everyone voted yes*)
theorem ac3:
  assumes ‹execute tupac_step (λp. Initial (init_val p) UNIV r) UNIV events msgs states›
    and ‹states 0 = Committed a b› 
  shows ‹∀p ∈ UNIV. p ≠ 0 ⟶ (∃rcpt. (p, Send rcpt Yes) ∈ msgs)›
proof -
  have "inv11 msgs states UNIV"
    using assms invariants123 by blast
  then show ?thesis
    using assms inv11_def by metis
qed

lemma execute_prefix:
  assumes "execute step init procs events msgs states"
  and "events = a @ b"
  shows "∃msgs' states'. execute step init procs a msgs' states'"
  using assms
proof (induction arbitrary: a b rule: execute.induct)
  case (1 step init procs)
  then show ?case 
    using execute.intros(1) by blast
next
  case (2 step init procs events msgs states proc event new_state sent events' msgs' states')
  show ?case
    apply(cases "b = []")
     apply (metis "2.hyps"(1,2,3,4,5) "2.prems" execute.intros(2) self_append_conv)
    by (metis "2.IH" "2.hyps"(5) "2.prems" butlast_append butlast_snoc)
qed

lemma execute_deterministic:
  assumes "execute step init procs events msgs1 states1"
      and "execute step init procs events msgs2 states2"
  shows "msgs1 = msgs2 ∧ states1 = states2"
  using assms
proof (induction arbitrary: msgs2 states2 rule: execute.induct)
  case (1 step init procs)
  then show ?case 
    by (auto elim: execute.cases)
next
  case (2 step init procs events msgs states proc event new_state sent events' msgs' states')
  then show ?case
    by force
qed

lemma execute_msgs_mono:
  assumes "execute step init procs events msgs states"
    and "events' = events @ [e]"
    and "execute step init procs events' msgs' states'"
  shows "msgs ⊆ msgs'"
proof -
  obtain p sent msgs_prev states_prev where
    "msgs' = msgs_prev ∪ ((λmsg. (p, msg)) ` sent)"
    "execute step init procs events msgs_prev states_prev"
    using assms(2,3) by (auto elim: execute.cases)
  then have"msgs = msgs_prev"
    using assms(1) execute_deterministic by metis
  then show ?thesis 
    using ‹msgs' = msgs_prev ∪ ((λmsg. (p, msg)) ` sent)› by simp
qed

lemma execute_msgs_subset:
  assumes "execute step init procs events msgs states"
    and "events = a @ b"
    and "execute step init procs a msgs' states'"
  shows "msgs' ⊆ msgs"
using assms proof(induction b arbitrary: msgs states msgs' states' events rule: List.rev_induct)
  case Nil
  then show ?case
    using execute_deterministic Nil(1,3) by fastforce
next
  case (snoc b bs)
  then obtain events' where "events' = a @ bs"
    by fastforce
  then obtain msgs_short states_short where "execute step init procs events' msgs_short states_short"
    using snoc(2,3) execute_prefix by (metis append_assoc)
  then have "msgs_short ⊆ msgs"
    using snoc by (simp add: ‹events' = a @ bs› execute_msgs_mono)
  moreover have "msgs' ⊆ msgs_short"
    using snoc ‹execute step init procs events' msgs_short states_short› ‹events' = a @ bs› by metis
  ultimately show ?case
    by order
qed

lemma execute_step_from_trace:
  assumes "execute step init procs events msgs' states'"
    and "events = a @ [(p,e)] @ b"
    and "execute step init procs a msgs states"
    and "step p (states p) e = (new_state, sent)"
  shows "execute step init procs (a@[(p,e)]) (msgs ∪ ((λmsg. (p, msg)) ` sent)) (states(p:=new_state))"
  proof -
  ― ‹1. Show that the prefix (a @ [(p,e)]) is executable›
  obtain msgs_ae states_ae where 
    exec_ae: "execute step init procs (a @ [(p,e)]) msgs_ae states_ae"
    using execute_prefix assms(1-2) by (metis append_assoc)
  ― ‹2. Invert the execution of the prefix to get the properties of the last step›    
  then obtain msgs_prev states_prev ns_prev sent_prev where
    exec_prev: "execute step init procs a msgs_prev states_prev" and
    p_in: "p ∈ procs" and
    valid: "valid_event e p msgs_prev" and
    step_prev: "step p (states_prev p) e = (ns_prev, sent_prev)" and
    msgs_ae_def: "msgs_ae = msgs_prev ∪ ((λmsg. (p, msg)) ` sent_prev)" and
    states_ae_def: "states_ae = states_prev(p := ns_prev)"
    by auto
  ― ‹3. Use determinism to show the state 'a' in the trace is exactly the 'a' we assumed›
  then have "msgs = msgs_prev" "states = states_prev"
    using execute_deterministic by (metis assms(3))+
  ― ‹4. Substitute our known 'states' and 'msgs' into the transition properties›
  moreover have "ns_prev = new_state" and "sent_prev = sent"
    using step_prev assms(4) calculation by auto
  ― ‹5. Reconstruct the execution step using the introduction rule›
  ultimately show ?thesis
    using exec_ae msgs_ae_def states_ae_def by fastforce
qed

lemma noStart_init:
  assumes "execute tupac_step (λp. Initial (init_val p) UNIV r) UNIV events msgs states"
    and "∀p. (p, Timeout) ∉ set events ∧ (p, Restart) ∉ set events ∧ (0, Start) ∉ set events"
  shows "∀p. states p = Initial (init_val p) UNIV r"
using assms proof (induction events arbitrary: msgs states rule: List.rev_induct)
  case Nil
  then show ?case
    using execute_init by blast
next
  case (snoc x xs)
  obtain proc event where x_eq: "x = (proc, event)"
    by fastforce
  obtain msgs' states' where ex_xs: "execute tupac_step (λp. Initial (init_val p) UNIV r) UNIV xs msgs' states'"
    using snoc.prems(1) execute_prefix by blast
  have IH: "∀p. states' p = Initial (init_val p) UNIV r"
    using snoc.IH[OF ex_xs] snoc.prems(2) by simp
  obtain new_state sent where step: "tupac_step proc (states' proc) event = (new_state, sent)"
    by force
  have ex_snoc: "execute tupac_step (λp. Initial (init_val p) UNIV r) UNIV (xs @ [x]) (msgs' ∪ Pair proc ` sent) (states'(proc := new_state))"
    using ex_xs step x_eq execute_step by (smt (verit) execute.intros(2) execute_deterministic snoc.prems(1))
  have states_eq: "states = states'(proc := new_state)" 
   and msgs_eq: "msgs = msgs' ∪ Pair proc ` sent"
    using snoc.prems(1) ex_snoc execute_deterministic by metis+
  have coordinatorInit:"states 0 = Initial (init_val 0) UNIV r"
  proof (cases "proc = 0")
    case True
    with snoc.prems(2) x_eq have "event ≠ Timeout ∧ event ≠ Restart ∧ event ≠ Start"
      by fastforce
    then obtain sender msg where "event = Receive sender msg"
      by (meson event.exhaust)
    with True step IH states_eq show ?thesis
      by simp
  next
    case False
    then show ?thesis
      using states_eq IH by simp
  qed
  moreover have "inv41 msgs states"
    using invariant41 snoc.prems(1) by blast
  ultimately have no_msgs: "msgs = {}"
    unfolding inv41_def by blast
  then have noToRsRc:"event ≠ Timeout ∧ event ≠ Restart ∧ (proc ≠ 0 ⟶ (∀sender msg. event ≠ Receive sender msg))"
    using snoc.prems(2) x_eq ex_snoc msgs_eq by auto
  have "new_state = Initial (init_val proc) UNIV r"
  proof(cases "proc = 0")
    case True
    then show ?thesis
      using coordinatorInit states_eq by auto
  next
    case False
    then show ?thesis
      by (metis IH event.exhaust local.step participant_step.simps(27) prod.inject tupac_step.elims noToRsRc)
  qed
  then show ?case
    using states_eq IH coordinatorInit by auto
qed


lemma execute_receive_event:
  assumes "execute step init procs events msgs states"
    and "(rcpt, Receive sender msg) ∈ set events"
  shows "(sender, Send rcpt msg) ∈ msgs"
proof -
  obtain pevents fevents where split:"events = (pevents@[(rcpt, Receive sender msg)])@fevents"
    by (metis append.left_neutral append_Cons assms(2) in_set_conv_decomp_first append.assoc)
  then obtain msgs' states' where prefix_ex:"execute step init procs (pevents@[(rcpt, Receive sender msg)]) msgs' states'"
    using execute_prefix by (metis append.assoc assms(1))
  then have "(sender, Send rcpt msg) ∈ msgs'"
    using execute_receive by metis
  moreover have "msgs' ⊆ msgs"
    using assms(1) split prefix_ex execute_msgs_subset by meson
  ultimately show ?thesis
    by fast
qed

lemma
  assumes "execute tupac_step (λp. Initial (init_val p) UNIV r) UNIV beforeStart msgs states"
    and "∀p. states p = Initial (init_val p) UNIV r"
    and "execute tupac_step (λp. Initial (init_val p) UNIV r) UNIV (beforeStart@[(0,Start)]@beforePrepare) msgs' states'"
    and "∀p. (p, Timeout) ∉ set beforePrepare ∧ (p, Restart) ∉ set beforePrepare ∧ (p, Receive 0 (Prepare (init_val 0))) ∉ set beforePrepare"
    and "p ≠ 0"
  shows "states' p = Initial (init_val p) UNIV r"
  using assms 
proof (induction beforePrepare arbitrary: msgs' states' rule: List.rev_induct)
  case Nil
    obtain msgs1 states1 where exNil:"execute tupac_step (λp. Initial (init_val p) UNIV r) UNIV (beforeStart@[(0,Start)]) msgs1 states1"
      using execute_prefix assms(3) by (metis append_assoc)
    moreover have "tupac_step 0 (states 0) Start = (Collecting (init_val 0) UNIV {0} r, {Send p (Prepare (init_val 0)) | p. p ∈ UNIV})"
      using assms(1,2) by auto
    moreover have "execute tupac_step (λp. Initial (init_val p) UNIV r) 
                                    UNIV 
                                    (beforeStart@[(0,Start)]) 
                                    (msgs ∪ ((λmsg. (0, msg)) ` {Send p (Prepare (init_val 0)) | p. p ∈ UNIV})) 
                                    (states(0:=Collecting (init_val 0) UNIV {0} r))"
      using calculation assms(1) by (simp add: execute_step_from_trace)
    ultimately have "states1 p = Initial (init_val p) UNIV r"
      by (metis (mono_tags, lifting) assms(2) fun_upd_apply assms(5) execute_deterministic)
    moreover have "states1 = states'"
      using Nil exNil assms execute_deterministic by (metis append.right_neutral)
    ultimately show ?case
      by simp
  next
    case (snoc x xs)
    then obtain proc event where "x = (proc, event)"
      by fastforce
    have invariants:"inv42 msgs' ∧ inv43 msgs' (init_val 0)"
      using snoc(4) sorry
    have noPrep:"∀proc t. (p, Receive proc (Prepare t)) ∉ set (xs @ [x])"
    proof(rule ccontr)
      assume "¬(∀proc t. (p, Receive proc (Prepare t)) ∉ set (xs @ [x]))"
      then have "∃proc t. (p, Receive proc (Prepare t)) ∈ set (xs @ [x])"
        by blast
      then obtain proc t where ev_props:"(p, Receive proc (Prepare t)) ∈ set (xs @ [x])"
        by fastforce
      then have "(proc, Send p (Prepare t)) ∈ msgs'"
        using execute_receive_event snoc(4) execute_prefix by fastforce
      moreover from this have "(0, Send p (Prepare (init_val 0))) ∈ msgs'"
        using inv42_def inv43_def by (metis invariants)
      ultimately show "False"
        by (metis  inv42_def inv43_def invariants snoc(5) ev_props)
    qed
(*Thus such an Receive Prepare event cannot occur. 
  Furthermore there are no Timeouts nor restarts. 
  Thus the state of p does not change
  Since it was Initial ... before it is also now*)
    then show ?case
    proof(cases "proc = p")
      case True
      then have "(∀proc t. event ≠ Receive proc (Prepare t)) ∧ event ≠ Timeout ∧ event ≠ Restart"
        using snoc(5) ‹x = (proc, event)› noPrep by fastforce
      then have "states' p = Initial (init_val p) UNIV r"
        sorry
      then show ?thesis
        by presburger
    next
      case False
      then have "states' p = states p"
        sorry
      then show ?thesis
        using snoc(3) by presburger
    qed
qed

(*if no failures and all processes vote yes then commit*)
theorem ac4:
  assumes valid_exec:‹execute tupac_step (λp. Initial (init_val p) UNIV r) UNIV events msgs states›
    and initiated:‹(0,Start) ∈ set events›
    and no_fail:‹∀p. (p, Timeout) ∉ set events ∧ (p, Restart) ∉ set events›
    and all_yes:‹∀p ∈ UNIV. p ≠ 0 ⟶ (∃rcpt. (p, Send rcpt Yes) ∈ msgs)›
    and participant_exists:‹∃p. p ∈ UNIV ∧ p ≠ 0›
    and delivery: ‹∀pevents fevents proc event. events = pevents@[(proc, event)]@fevents ⟶ 
      (∃msgs states new_state sent. 
        tupac_step proc (states proc) event = (new_state, sent) ∧
        execute tupac_step (λp. Initial (init_val p) UNIV r) UNIV pevents msgs states ∧ 
        (∀rcpt msg. 
        (Send rcpt msg) ∈ sent ⟶ 
        (rcpt, Receive proc msg) ∈ set fevents))›
  shows "∀sender rcpt. (sender, Send rcpt Abort) ∉ msgs" (*What better to show here?*)
proof -
  obtain beforeStart afterStart where split:"events = beforeStart@[(0, Start)]@afterStart" 
                                  and noStart:"(0, Start) ∉ set beforeStart"
    using assms(2) by (metis append_Cons append_Nil split_list_first)
  then have all_receives:"∀p ∈ UNIV. p ≠ 0 ⟶ ((p, Receive 0 (Prepare (init_val 0))) ∈ set afterStart)"
  proof -
    obtain msgs_bs states_bs preparing prepareMsgs where val_ex_bs:"execute tupac_step (λp. Initial (init_val p) UNIV r) UNIV beforeStart msgs_bs states_bs"
                                                      and step_start:"tupac_step 0 (states_bs 0) Start = (preparing, prepareMsgs)"
                                                      and deliver:"(∀rcpt msg. (Send rcpt msg) ∈ prepareMsgs ⟶ 
                                                              (rcpt, Receive 0 msg) ∈ set afterStart)"
      using split delivery by metis
    moreover have ‹∀p. (p, Timeout) ∉ set beforeStart ∧ (p, Restart) ∉ set beforeStart›
      using split no_fail by simp
    ultimately have "states_bs 0 = Initial (init_val 0) UNIV r"
      using noStart noStart_init by blast
    then have "tupac_step 0 (states_bs 0) Start = (Collecting (init_val 0) UNIV {0} r, {Send p (Prepare (init_val 0)) | p. p ∈ UNIV})"
      by simp
    then have "(∀rcpt msg. (Send rcpt msg) ∈ {Send p (Prepare (init_val 0)) | p. p ∈ UNIV} ⟶ (rcpt, Receive 0 msg) ∈ set afterStart)"
      using deliver step_start by auto
    then show ?thesis
      by blast
  qed
  have all_send_yes: "∀p. p ∈ UNIV ∧ p ≠ 0 ⟶ (0, Receive p Yes) ∈ set afterStart" (* Replace sent_by_p with your actual msg set logic *)
  proof
    fix p::'a
    show "p ∈ UNIV ∧ p ≠ 0 ⟶ (0, Receive p Yes) ∈ set afterStart"
    proof
      assume participant:"p ∈ UNIV ∧ p ≠ 0"
        (* Since this p must have received the Prepare message... *)
      then have "(p, Receive 0 (Prepare (init_val 0))) ∈ set afterStart"
        using all_receives by simp
      then obtain beforePrepare afterPrepare where splitPrep:"afterStart = beforePrepare@[(p, Receive 0 (Prepare (init_val 0)))]@afterPrepare" 
                                  and noPrepare:"(p, Receive 0 (Prepare (init_val 0))) ∉ set beforePrepare"
        by (metis append.left_neutral append_Cons split_list_first)
      then have eventSplit:"events = beforeStart@[(0,Start)]@beforePrepare@[(p, Receive 0 (Prepare (init_val 0)))]@afterPrepare"
        using split by simp
      then have "(∃msgs states new_state sent.
           tupac_step p (states p) (Receive 0 (Prepare (init_val 0))) = (new_state, sent) ∧
           execute tupac_step (λp. Initial (init_val p) UNIV r) UNIV (beforeStart@[(0,Start)]@beforePrepare) msgs states ∧
           (∀rcpt msg. Send rcpt msg ∈ sent ⟶ (rcpt, Receive p msg) ∈ set afterPrepare))"
        using delivery by auto
      then obtain msgs_bp states_bp prepared yesMsgs where val_ex_bs:"execute tupac_step (λp. Initial (init_val p) UNIV r) UNIV (beforeStart@[(0,Start)]@beforePrepare) msgs_bp states_bp"
                                                      and step_prepare:"tupac_step p (states_bp p) (Receive 0 (Prepare (init_val 0))) = (prepared, yesMsgs)"
                                                      and deliver:"(∀rcpt msg. (Send rcpt msg) ∈ yesMsgs ⟶ 
                                                              (rcpt, Receive p msg) ∈ set afterStart)"
        using delivery participant splitPrep by auto

      then have "states_bp p = Initial (init_val 0) UNIV r"
        using noPrepare val_ex_bs sorry
      then have "tupac_step p (states_bp p) (Receive 0 (Prepare (init_val 0))) = (Prepared, {Send 0 Yes})"
        sorry
      then have "(∀rcpt msg. (Send rcpt msg) ∈ {Send 0 Yes} ⟶ (rcpt, Receive p msg) ∈ set afterStart)"
        using deliver step_prepare sorry
      show "(0, Receive p Yes) ∈ set afterStart"
        using splitPrep deliver sorry
    qed
  qed
  then show ?thesis
    sorry
  (* 5. Now that everyone sent Yes, use the delivery assumption to show the Coordinator receives them - DONE*)
  (* ... Then split the trace again to find when the coordinator receives the LAST Yes ... *)
  (* Show that the coordinator is in Committed after processing every Yes event <-- ! ! !*)
qed

end