theory Automata_inv_1
  imports Automata_inv_def
begin

lemma parts_trans_proj:
  assumes "(s, a, s') \<in> parts_trans P"
  shows "if p \<in> P \<and> ((\<exists>q m. a = Receive q p m) \<or> a = Timeout p \<or> a = Restart p \<or> (\<exists>q m. a = Send p q m))
         then (s p, a, s' p) \<in> part_trans p
         else s' p = s p"
  using assms unfolding parts_trans_def by auto

lemma parts_trans_Send:
  assumes "(pstates, Send sender rcpt msg, pstates') \<in> parts_trans P"
  shows "\<forall>p state1 msgs1 state2 msgs2. pstates p = PState state1 msgs1 \<and> pstates' p = PState state2 msgs2 \<longrightarrow> state1 = state2"
proof clarify
  fix p state1 msgs1 state2 msgs2
  assume pre1: "pstates p = PState state1 msgs1"
  assume pre2: "pstates' p = PState state2 msgs2"
  have step: "if p \<in> P \<and> sender = p 
              then (pstates p, Send sender rcpt msg, pstates' p) \<in> part_trans p
              else pstates' p = pstates p"
    using parts_trans_proj[OF assms, of p] by auto
  show "state1 = state2"
  proof (cases "p \<in> P \<and> sender = p")
    case True
    then have "(PState state1 msgs1, Send p rcpt msg, PState state2 msgs2) \<in> part_trans p"
      using pre1 pre2 step by auto
    then show ?thesis 
      by (elim part_trans_inv) auto
  next
    case False
    then have "pstates' p = pstates p" 
      using step by auto
    then show ?thesis 
      using pre1 pre2 by auto
  qed
qed

lemma parts_trans_step_result:
  assumes "(pstates, a, pstates') \<in> parts_trans P"
    and "pstates rcpt = PState pstate pmsgs"
    and "participant_step rcpt pstate a = (new_state, sent)"
    and "rcpt \<in> P"
    and "a = Receive s rcpt m \<or> a = Timeout rcpt \<or> a = Restart rcpt"
  shows "pstates' rcpt = PState new_state (pmsgs \<union> ((\<lambda>msg. (rcpt, msg)) ` sent))"
proof -
  from assms(1,4,5) have "(pstates rcpt, a, pstates' rcpt) \<in> part_trans rcpt"
    unfolding parts_trans_def by auto
  thus ?thesis
    using assms(2,3,5) unfolding part_trans_def by auto
qed

lemma System_Receive_chan_step:
  assumes "(((c, ch), p), Receive sender rcpt msg, ((c', ch'), p')) \<in> trans_of (System t P r)"
  shows "(sender, rcpt, msg) \<in> ch \<and> ch' = ch"
  using assms 
  unfolding System_def par_def trans_of_def asig_comp_def ioa_projections Coordinator_def Channel_def Participants_def 
  asig_inputs_def asig_outputs_def asig_internals_def actions_def coord_asig_def chan_asig_def  apply auto
    apply (metis (lifting) action.distinct(9) action.inject(3) chan_trans_inv)
   apply (metis action.distinct(9) chan_trans_inv)
  by (metis action.distinct(9) chan_trans_inv)

lemma invariant1_trans:
  assumes "reachable (System t (UNIV - {0}) r) s"
    and "inv1 s"
    and "(s, a, s') \<in> trans_of (System t (UNIV - {0}) r)"
  shows "inv1 s'"
proof -
  obtain cstate cmsgs chmsgs pstates where decomp_s: "s = ((CState cstate cmsgs, chmsgs), pstates)"
    by (metis coord_state.exhaust surj_pair)
  obtain cstate' cmsgs' chmsgs' pstates' where decomp_s': "s' = ((CState cstate' cmsgs', chmsgs'), pstates')"
    by (metis coord_state.exhaust surj_pair)
  show ?thesis
    using assms(3) unfolding decomp_s decomp_s'
  proof (induction rule: System_trans_inv)
    case System_Step
    then show ?case
    proof(cases a)
      case (Start rcpt)
      then have "pstates = pstates'"
        using System_Step(3) unfolding parts_trans_def by auto
      moreover have "chmsgs = chmsgs'"
        using Start System_Step(2) by auto
      ultimately have "inv1 s \<longleftrightarrow> inv1 s'"
        using inv1_def by (metis assms(2) decomp_s decomp_s' fst_conv snd_conv)
      then show ?thesis 
        using assms(2) decomp_s decomp_s' by simp
    next
      case (Send sender rcpt _)
      then have "(\<exists>msgs p. pstates p = PState PCommitted msgs) \<longleftrightarrow> (\<exists>msgs p. pstates' p = PState PCommitted msgs)"
        by (metis System_Step.hyps(3) part_state.exhaust parts_trans_Send)
      moreover have "(\<exists>sender rcpt. (sender, rcpt, Commit) \<in> chmsgs) \<longrightarrow> (\<exists>sender rcpt. (sender, rcpt, Commit) \<in> chmsgs')"
        using Send System_Step(2) by auto
      ultimately have "inv1 s \<longleftrightarrow> inv1 s'"
        using inv1_def by (metis assms(2) decomp_s decomp_s' fst_conv snd_conv)
      then show ?thesis
        using assms(2) decomp_s decomp_s' by simp
    next
      case (Receive sender rcpt msg)
      have chEquiv:"chmsgs = chmsgs'"
        using Receive System_Step(2) by blast
      moreover have receive:"(sender, rcpt, msg) \<in> chmsgs'"
        by (metis Receive decomp_s decomp_s' System_Receive_chan_step assms(3))
      then show ?thesis
      proof(cases "rcpt = 0")
        case True
        then have "pstates = pstates'"
          using True System_Step(3) Receive unfolding parts_trans_def by auto
        then have "inv1 s \<longleftrightarrow> inv1 s'"
          using inv1_def chEquiv by (metis decomp_s decomp_s' fst_conv snd_conv)
        then show ?thesis
          using assms(2) decomp_s decomp_s' by simp
      next
        case False
        then have otherPartsEquiv:"\<forall>p \<noteq> rcpt. pstates p = pstates' p"
          using System_Step(3) Receive unfolding parts_trans_def by auto
        then show ?thesis
        proof(cases "pstates rcpt = pstates' rcpt")
          case True
          then have "pstates = pstates'"
            using otherPartsEquiv by auto
          then show ?thesis
            using chEquiv assms(2) inv1_def decomp_s decomp_s' by (metis fst_conv snd_conv)
        next
          case False
          then obtain pstate pmsgs where stateDecomp:"pstates rcpt = PState pstate pmsgs"
            using part_state.exhaust by blast
          then obtain new_state sent where step:"participant_step rcpt pstate a = (new_state, sent)"
            using System_Step(3) False by fastforce
          have update_eq: "pstates' rcpt = PState new_state (pmsgs \<union> ((\<lambda>msg. (rcpt, msg)) ` sent))"
            by (smt (verit, ccfv_SIG) step parts_trans_proj stateDecomp parts_trans_step_result System_Step(3) False Receive)
          then show ?thesis
          proof(cases pstate)
            case (PInitial v)
            then show ?thesis
            proof(cases "\<exists>t'. msg = Prepare t'")
              case True
              then obtain t' where "msg = Prepare t'"
                by auto
              then have "(new_state, sent) = (if v = t' then (Prepared, {(sender, Yes)}) else (PAborted, {(sender, No)}))"
                using Receive PInitial step by simp
              then have "new_state = Prepared \<or> new_state = PAborted"
                by (meson prod.inject)
              then have "\<forall>msgs. pstates' rcpt \<noteq> PState PCommitted msgs"
                using update_eq by auto
              then have "inv1 s \<longleftrightarrow> inv1 s'"
                by (metis assms(2) decomp_s decomp_s' fst_conv snd_conv inv1_def otherPartsEquiv chEquiv)
              then show ?thesis
                using assms(2) decomp_s decomp_s' by simp
            next
              case False
              then have "new_state = pstate \<and> sent = {}"
                using PInitial Receive local.step by (cases msg;auto)
              then have "pstates' rcpt = PState pstate pmsgs"
                using update_eq by simp
              then have "pstates = pstates'"
                using otherPartsEquiv stateDecomp by force
              then show ?thesis
                using \<open>pstates rcpt \<noteq> pstates' rcpt\<close> by presburger
            qed
          next
            case Prepared
            then show ?thesis
            proof(cases "msg = Commit")
              case True
              then have "(\<exists>sender rcpt. (sender, rcpt, Commit) \<in> snd (fst s))"
                using receive chEquiv decomp_s by auto
              then show ?thesis
                using assms(2) decomp_s decomp_s' by (simp add: chEquiv inv1_def)
            next
              case False
              then show ?thesis
              proof(cases "msg = Abort")
                case True
                then have "new_state = PAborted \<and> sent = {(sender, Ack)}"
                  using Receive Prepared step by simp
                then have "\<forall>msgs. pstates' rcpt \<noteq> PState PCommitted msgs"
                  using update_eq by simp
                then have "inv1 s \<longleftrightarrow> inv1 s'"
                  by (metis assms(2) decomp_s decomp_s' fst_conv snd_conv inv1_def otherPartsEquiv chEquiv)
                then show ?thesis
                  using assms(2) decomp_s decomp_s' by simp
              next
                case False
                then have "new_state = pstate \<and> sent = {}"
                  using Prepared Receive local.step \<open>msg \<noteq> Commit\<close> \<open>msg \<noteq> Abort\<close> by(cases msg; auto)
                then have "pstates' rcpt = PState pstate pmsgs"
                  using update_eq by simp
                then have "pstates = pstates'"
                  using otherPartsEquiv stateDecomp by force
                then show ?thesis
                  using \<open>pstates rcpt \<noteq> pstates' rcpt\<close> by presburger
              qed
            qed
          next
            case PCommitted
            then have "new_state = PCommitted"
              using step participant_step_inv by fastforce
            then have "inv1 s \<longleftrightarrow> inv1 s'"
              by (metis PCommitted stateDecomp assms(2) decomp_s decomp_s' fst_conv snd_conv inv1_def chEquiv)
            then show ?thesis
              using assms(2) decomp_s decomp_s' by simp
          next
            case PAborted
            then have "new_state = PAborted"
              using step participant_step_inv by fastforce
            then have "\<forall>msgs. pstates' rcpt \<noteq> PState PCommitted msgs"
              using update_eq by simp
            then have "inv1 s \<longleftrightarrow> inv1 s'"
              by (metis assms(2) decomp_s decomp_s' fst_conv snd_conv inv1_def chEquiv otherPartsEquiv)
            then show ?thesis
              using assms(2) decomp_s decomp_s' by simp
          qed
        qed
      qed
    next
      case (Timeout rcpt)
      have chEquiv:"chmsgs = chmsgs'"
        using Timeout System_Step(2) by blast
      then show ?thesis
      proof(cases "rcpt = 0")
        case True
        then have "pstates = pstates'"
          using True System_Step(3) Timeout unfolding parts_trans_def by auto
        then have "inv1 s \<longleftrightarrow> inv1 s'"
          using inv1_def chEquiv by (metis decomp_s decomp_s' fst_conv snd_conv)
        then show ?thesis
          using assms(2) decomp_s decomp_s' by simp
      next
        case False
        then have otherPartsEquiv:"\<forall>p \<noteq> rcpt. pstates p = pstates' p"
          using System_Step(3) Timeout unfolding parts_trans_def by auto
        then show ?thesis
        proof(cases "pstates rcpt = pstates' rcpt")
          case True
          then have "pstates = pstates'"
            using otherPartsEquiv by auto
          then show ?thesis
            using chEquiv assms(2) inv1_def decomp_s decomp_s' by (metis fst_conv snd_conv)
        next
          case False
          then obtain pstate pmsgs where stateDecomp:"pstates rcpt = PState pstate pmsgs"
            using part_state.exhaust by blast
          then obtain new_state sent where step:"participant_step rcpt pstate a = (new_state, sent)"
            using System_Step(3) False by fastforce
          have update_eq: "pstates' rcpt = PState new_state (pmsgs \<union> ((\<lambda>msg. (rcpt, msg)) ` sent))"
            by (smt (verit, ccfv_SIG) step parts_trans_proj stateDecomp parts_trans_step_result System_Step(3) False Timeout)
          then show ?thesis
          proof(cases pstate)
            case (PInitial v)
            then have "new_state = PAborted"
              using step participant_step_inv Timeout by fastforce
            then have "\<forall>msgs. pstates' rcpt \<noteq> PState PCommitted msgs"
              using update_eq by simp
            then have "inv1 s \<longleftrightarrow> inv1 s'"
              by (metis assms(2) decomp_s decomp_s' fst_conv snd_conv inv1_def chEquiv otherPartsEquiv)
            then show ?thesis
              using assms(2) decomp_s decomp_s' by simp
          next
            case Prepared
            then have "new_state = pstate \<and> sent = {}"
              using step Prepared Timeout by auto
            then have "pstates' rcpt = PState pstate pmsgs"
              using update_eq by simp
            then have "pstates = pstates'"
              using otherPartsEquiv stateDecomp by force
            then show ?thesis
              using \<open>pstates rcpt \<noteq> pstates' rcpt\<close> by presburger
          next
            case PCommitted
            then have "new_state = PCommitted"
              using step participant_step_inv by fastforce
            then have "inv1 s \<longleftrightarrow> inv1 s'"
              by (metis PCommitted stateDecomp assms(2) decomp_s decomp_s' fst_conv snd_conv inv1_def chEquiv)
            then show ?thesis
              using assms(2) decomp_s decomp_s' by simp
          next
            case PAborted
            then have "new_state = PAborted"
              using step participant_step_inv by fastforce
            then have "\<forall>msgs. pstates' rcpt \<noteq> PState PCommitted msgs"
              using update_eq by simp
            then have "inv1 s \<longleftrightarrow> inv1 s'"
              by (metis assms(2) decomp_s decomp_s' fst_conv snd_conv inv1_def chEquiv otherPartsEquiv)
            then show ?thesis
              using assms(2) decomp_s decomp_s' by simp
          qed
        qed
      qed
    next
      case (Restart rcpt)
      have chEquiv:"chmsgs = chmsgs'"
        using Restart System_Step(2) by blast
      then show ?thesis
      proof(cases "rcpt = 0")
        case True
        then have "pstates = pstates'"
          using True System_Step(3) Restart unfolding parts_trans_def by auto
        then have "inv1 s \<longleftrightarrow> inv1 s'"
          using inv1_def chEquiv by (metis decomp_s decomp_s' fst_conv snd_conv)
        then show ?thesis
          using assms(2) decomp_s decomp_s' by simp
      next
        case False
        then have otherPartsEquiv:"\<forall>p \<noteq> rcpt. pstates p = pstates' p"
          using System_Step(3) Restart unfolding parts_trans_def by auto
        then show ?thesis
        proof(cases "pstates rcpt = pstates' rcpt")
          case True
          then have "pstates = pstates'"
            using otherPartsEquiv by auto
          then show ?thesis
            using chEquiv assms(2) inv1_def decomp_s decomp_s' by (metis fst_conv snd_conv)
        next
          case False
          then obtain pstate pmsgs where stateDecomp:"pstates rcpt = PState pstate pmsgs"
            using part_state.exhaust by blast
          then obtain new_state sent where step:"participant_step rcpt pstate a = (new_state, sent)"
            using System_Step(3) False by fastforce
          have update_eq: "pstates' rcpt = PState new_state (pmsgs \<union> ((\<lambda>msg. (rcpt, msg)) ` sent))"
            by (smt (verit, ccfv_SIG) step parts_trans_proj stateDecomp parts_trans_step_result System_Step(3) False Restart)
          then show ?thesis
          proof(cases pstate)
            case (PInitial v)
            then have "new_state = PInitial v"
              using step participant_step_inv Restart by fastforce
            then have "\<forall>msgs. pstates' rcpt \<noteq> PState PCommitted msgs"
              using update_eq by simp
            then have "inv1 s \<longleftrightarrow> inv1 s'"
              by (metis assms(2) decomp_s decomp_s' fst_conv snd_conv inv1_def chEquiv otherPartsEquiv)
            then show ?thesis
              using assms(2) decomp_s decomp_s' by simp
          next
            case Prepared
            then have "new_state = pstate \<and> sent = {}"
              using step Prepared Restart by auto
            then have "pstates' rcpt = PState pstate pmsgs"
              using stateDecomp step parts_trans_def Prepared part_trans_def apply auto
              using update_eq by simp
            then have "pstates = pstates'"
              using otherPartsEquiv stateDecomp by force
            then show ?thesis
              using \<open>pstates rcpt \<noteq> pstates' rcpt\<close> by presburger
          next
            case PCommitted
            then have "new_state = PCommitted"
              using step participant_step_inv by fastforce
            then have "inv1 s \<longleftrightarrow> inv1 s'"
              by (metis PCommitted stateDecomp assms(2) decomp_s decomp_s' fst_conv snd_conv inv1_def chEquiv)
            then show ?thesis
              using assms(2) decomp_s decomp_s' by simp
          next
            case PAborted
            then have "new_state = PAborted"
              using step participant_step_inv by fastforce
            then have "\<forall>msgs. pstates' rcpt \<noteq> PState PCommitted msgs"
              using update_eq by simp
            then have "inv1 s \<longleftrightarrow> inv1 s'"
              by (metis assms(2) decomp_s decomp_s' fst_conv snd_conv inv1_def chEquiv otherPartsEquiv)
            then show ?thesis
              using assms(2) decomp_s decomp_s' by simp
          qed
        qed
      qed
    qed
  qed
qed

lemma invariant1:
  "invariant (System t (UNIV - {0}) r) inv1"
proof(induction rule: invariantI)
  case (1 s)
  moreover have "starts_of (System t (UNIV - {0}) r) = {((CState (CInitial (t 0) UNIV r) {},{}),\<lambda>p. PState (PInitial (t p)) {})}"
    unfolding starts_of_def System_def par_def Coordinator_def Channel_def Participants_def by auto
  ultimately have "s = ((CState (CInitial (t 0) UNIV r) {},{}),\<lambda>p. PState (PInitial (t p)) {})"
    by auto
  then show ?case 
    unfolding inv1_def by simp
next
  case (2 s t a)
  then show ?case
    using invariant1_trans by metis
qed

end