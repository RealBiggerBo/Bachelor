theory Automata_ac
  imports Automata_inv_1
          Automata_inv_111314 
          Automata_inv_15110
          Automata_inv_17 
          Automata_inv_3 
          Automata_inv_111
begin

definition process_committed where
  "process_committed p s \<longleftrightarrow> 
    (if p = 0 then (\<exists>a ack cmsgs. fst (fst s) = CState (CCommitted a ack) cmsgs)
     else (\<exists>m. (snd s) p = PState PCommitted m))"

definition process_aborted where
  "process_aborted p s \<longleftrightarrow> 
    (if p = 0 then (\<exists>a ack cmsgs. fst (fst s) = CState (CAborted a ack) cmsgs)
     else (\<exists>m. (snd s) p = PState PAborted m))"

lemma ac1_NoCoordinator:
  assumes "reachable (System t (UNIV - {0}) r) s"  
    and "proc1 \<noteq> 0 \<and> proc2 \<noteq> 0"
    and "process_committed proc1 s \<or> process_aborted proc1 s"
    and "process_committed proc2 s \<or> process_aborted proc2 s"
  shows "process_committed proc1 s \<longleftrightarrow> process_committed proc2 s"
proof (rule ccontr)
  assume asm1:"\<not>(process_committed proc1 s \<longleftrightarrow> process_committed proc2 s)"
  have inv:"inv1 s \<and> inv3 s \<and> inv11 UNIV s \<and> inv17 s"
    by (metis (mono_tags, lifting) invariantE invariant1 invariant3 invariants111314 invariant17 assms(1))
  then show "False"
  proof(cases "process_committed proc1 s")
    case True
    then have proc2Abort:"process_aborted proc2 s"
      using asm1 assms(4) by auto
    have commitMsg:"(\<exists>sender rcpt. (sender, rcpt, Commit) \<in> snd (fst s))"
      using True inv inv1_def assms(2) process_committed_def by metis
    then have noAbort:"(\<forall>sender recpt. (sender, recpt, Abort) \<notin> snd (fst s))"
      using inv inv3_def by metis
    then have "(\<forall>p \<in> UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, rcpt, Yes) \<in> snd (fst s)))"
      using inv inv11_def by (metis commitMsg)
    then have "\<exists>rcpt. (proc2, rcpt, Yes) \<in> snd (fst s)"
      using assms(2) by auto
    moreover have "\<forall>rcpt. (proc2, rcpt, Yes) \<notin> snd (fst s)"
      using proc2Abort assms(2) noAbort inv inv17_def by (metis process_aborted_def)
    ultimately show ?thesis
      by simp
  next
    case False
    then have Aborted: "process_aborted proc1 s"
      using assms(3) by auto
    then have Committed: "process_committed proc2 s"
      using asm1 assms(4) by (metis False)
    then have commitMsg:"(\<exists>sender rcpt. (sender, rcpt, Commit) \<in> snd (fst s))"
      using inv inv1_def assms(2) process_committed_def by metis
    then have noAbort:"(\<forall>sender recpt. (sender, recpt, Abort) \<notin> snd (fst s))"
      using inv inv3_def by metis
    then have "(\<forall>p \<in> UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, rcpt, Yes) \<in> snd (fst s)))"
      using inv inv11_def by (metis commitMsg)
    then have "\<exists>rcpt. (proc1, rcpt, Yes) \<in> snd (fst s)"
      using assms(2) by auto
    moreover have "\<forall>rcpt. (proc1, rcpt, Yes) \<notin> snd (fst s)"
      using Aborted assms(2) noAbort inv inv17_def by (metis process_aborted_def)
    ultimately show ?thesis
      by simp
  qed
qed

lemma ac1_OneCoordinator:
  assumes "reachable (System t (UNIV - {0}) r) s"
    and "p \<noteq> 0 "
    and "process_committed 0 s \<or> process_aborted 0 s"
    and "process_committed p s \<or> process_aborted p s"
  shows "process_committed 0 s \<longleftrightarrow> process_committed p s"
proof
  assume asmCommitted:"process_committed 0 s"
  have inv:"inv11 UNIV s \<and> inv17 s \<and> inv15 s"
    by (metis (no_types, lifting) invariant17 invariants111314 invariants15110 assms(1) invariantE assms(1))
  show "process_committed p s"
  proof(rule ccontr)
    assume asmAborted: "\<not>process_committed p s"
    then have proc2Abort: "process_aborted p s"
      using assms(4) by auto
    have "\<forall>p \<in> UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, rcpt, Yes) \<in> snd (fst s))"
      using inv inv11_def by (metis asmCommitted process_committed_def)
    then have "\<exists>rcpt. (p, rcpt, Yes) \<in> snd (fst s)"
      using assms(2) by auto
    moreover have noAbort:"\<forall>sender rcpt. (sender, rcpt, Abort) \<notin> snd (fst s)"
      using inv15_def asmCommitted inv by (metis process_committed_def)
    moreover have "\<forall>rcpt. (p, rcpt, Yes) \<notin> snd (fst s)"
      using proc2Abort assms(2) noAbort inv inv17_def by (metis process_aborted_def)
    ultimately show "False"
      by simp
  qed
next
  assume asmCommitted:"process_committed p s"
  have inv:"inv1 s \<and> inv111 s"
    using invariant111 invariant1 invariant111 assms(1) invariantE by metis
  have commitMsg:"(\<exists>sender rcpt. (sender, rcpt, Commit) \<in> snd (fst s))"
    using inv asmCommitted inv1_def assms(2) process_committed_def by metis
  then have "\<exists>all ack msgs. fst (fst s) = CState (CCommitted all ack) msgs \<or> fst (fst s) = CState Forgotten msgs"
    using inv inv111_def by metis
  then show "process_committed 0 s"
    by (metis assms(3) coord_state.inject cstate.distinct(19) process_aborted_def process_committed_def)
qed

text \<open>All processes that decide must decide on the same value\<close>
lemma ac1_Theorem:
  assumes "reachable (System t (UNIV - {0}) r) s"
    and "process_committed proc1 s \<or> process_aborted proc1 s"
    and "process_committed proc2 s \<or> process_aborted proc2 s"
  shows "process_committed proc1 s \<longleftrightarrow> process_committed proc2 s"
proof(cases "proc1 = proc2")
  case True
  then show ?thesis 
    by auto
next
  case False
  then show ?thesis
  proof(cases "proc1 = 0 \<or> proc2 = 0")
    case True
    then show ?thesis
      using ac1_OneCoordinator assms by metis
  next
    case False
    then have "proc1 \<noteq> 0 \<and> proc2 \<noteq> 0"
      by simp
    then show ?thesis
      using ac1_NoCoordinator assms by metis
  qed
qed

end