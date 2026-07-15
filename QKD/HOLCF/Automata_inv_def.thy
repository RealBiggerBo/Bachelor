theory Automata_inv_def
  imports Automata_2PC
begin


definition inv1 where
  \<open>inv1 s \<longleftrightarrow>
     ((\<exists>msgs p. (snd s) p = PState PCommitted msgs) \<longrightarrow>
                 (\<exists>sender rcpt. (sender, rcpt, Commit) \<in> snd (fst s)))\<close>

definition inv11 where
  \<open>inv11 procs s \<longleftrightarrow>
    ((\<exists>sender rcpt. (sender, rcpt, Commit) \<in> snd (fst s)) \<or> (\<exists>all ack msgs. fst (fst s) = CState (CCommitted all ack) msgs) \<longrightarrow>
                 (\<forall>p \<in> procs. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, rcpt, Yes) \<in> snd (fst s))))\<close>

definition inv13 where
  \<open>inv13 procs s \<longleftrightarrow>
    (\<forall>t all yes r msgs. fst (fst s) = CState (Collecting t all yes r) msgs \<longrightarrow> 
                (procs = all \<and> (\<forall>p \<in> yes. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, rcpt, Yes) \<in> snd (fst s)))))\<close>

definition inv14 where
  \<open>inv14 procs s \<longleftrightarrow>
    (\<forall>t all r msgs. fst (fst s) = CState (CInitial t all r) msgs \<longrightarrow> procs = all)\<close>

definition inv15 where
  \<open>inv15 s \<longleftrightarrow>
    ((\<exists>t all yes r msgs. fst (fst s) = CState (CInitial t all r) msgs \<or> fst (fst s) = CState (Collecting t all yes r) msgs \<or> fst (fst s) = CState (CCommitted all yes) msgs) \<longrightarrow> 
              (\<forall>sender rcpt. (sender, rcpt, Abort) \<notin> snd (fst s)))\<close>

definition inv17 where
  \<open>inv17 s \<longleftrightarrow>
    (\<forall>p. p \<noteq> 0 \<and> (\<exists>msgs. (snd s) p = PState PAborted msgs) \<and> (\<forall>sender recpt. (sender, recpt, Abort) \<notin> snd (fst s)) \<longrightarrow> (\<forall>rcpt. (p, rcpt, Yes) \<notin> snd (fst s)))\<close>

definition inv110 where
  \<open>inv110 s \<longleftrightarrow>
    ((\<exists>t all yes r msgs. fst (fst s) = CState (CInitial t all r) msgs \<or> fst (fst s) = CState (Collecting t all yes r) msgs \<or> fst (fst s) = CState (CAborted all yes) msgs) \<longrightarrow> 
              (\<forall>sender rcpt. (sender, rcpt, Commit) \<notin> snd (fst s)))\<close>

definition inv111 where
  \<open>inv111 s \<longleftrightarrow>
    ((\<exists>sender rcpt. (sender, rcpt, Commit) \<in> snd (fst s)) \<longrightarrow>
     (\<exists>all ack cmsgs. fst (fst s) = CState (CCommitted all ack) cmsgs \<or> fst (fst s) = CState Forgotten cmsgs))\<close>

definition inv3 where
  \<open>inv3 s \<longleftrightarrow>
    (\<exists>sender recpt. (sender, recpt, Commit) \<in> snd (fst s)) \<longrightarrow> (\<forall>sender recpt. (sender, recpt, Abort) \<notin> snd (fst s))\<close>

definition inv_part_commit_msg  where
  \<open>inv_part_commit_msg s \<longleftrightarrow>
    (\<forall>p. (\<exists>msgs. (snd s) p = PState PCommitted msgs) \<longrightarrow> 
      (\<exists>sender rcpt. (sender, rcpt, Commit) \<in> snd (fst s)))\<close>

end