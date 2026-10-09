theory QKD_System_Helpers_QKD_Trans_Elim
  imports QKD_System_Helpers_Trans_Elim QKD_System_ActsDisj
begin

context QKD_Network
begin

lemma qkd_invariant_step[consumes 4, case_names 
    GetKey_Gen
    GetKeyWithID_Reserve
    Send]:
  assumes "reachable System.ioa s"
    and "P s"
    and "a \<in> act qkd_layer.ioa"
    and "s = (apps, kmes, bridges, qkd, net)"
    and "t = (apps, kmes, bridges, qkd', net')"
    and "\<And>pid gen sent sender target keyID keyVal.
         \<lbrakk>pid \<in> qkdID ` (\<Union>(bridgeIDs ` nodes));
          keyID \<notin> fst ` ((snd ` gen) \<union> sent);
          a = Receive sender pid (GetKey pid target); net = net';
          qkd  = QKD gen sent;
          qkd' = QKD (gen \<union> {(sender, keyID, keyVal)}) sent\<rbrakk> \<Longrightarrow> P t"
    and "\<And>pid gen sent sender target keyID keyVal.
         \<lbrakk>pid \<in> qkdID ` (\<Union>(bridgeIDs ` nodes));
          (keyID, keyVal) \<in> sent;
          a = Receive sender pid (GetKeyWithID pid target keyID); net = net';
          qkd  = QKD gen sent;
          qkd' = QKD (gen \<union> {(sender, keyID, keyVal)}) (sent - {(keyID, keyVal)})\<rbrakk> \<Longrightarrow> P t"
    and "\<And>pid gen sent rcpt target keyID keyVal.
         \<lbrakk>pid \<in> qkdID ` (\<Union>(bridgeIDs ` nodes));
          (rcpt, keyID, keyVal) \<in> gen;
          a = Send pid rcpt (KeyResponse keyID keyVal); 
          net' = net \<union> {(pid, rcpt, KeyResponse keyID keyVal)};
          qkd  = QKD gen sent;
          qkd' = QKD (gen - {(rcpt, keyID, keyVal)}) (sent \<union> {(keyID, keyVal)})\<rbrakk> \<Longrightarrow> P t"
  shows "s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t \<longrightarrow> P t"
proof
  assume sat_trans:"s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t"
  note sys_trans = System_trans_elim[OF sat_trans assms(4,5)]
  consider "\<exists>sender pid msg. a = Receive sender pid msg \<and> pid \<in> qkdID ` (\<Union>(bridgeIDs ` nodes))" 
          | "\<exists>pid rcpt msg. a = Send pid rcpt msg \<and> pid \<in> qkdID ` (\<Union>(bridgeIDs ` nodes))"
    using assms(3,4) unfolding actions_def asig_projections asig_of_def apply simp
    unfolding qkd_layer.asig by force
  then show "P t"
  proof cases
    case 1
    then obtain sender pid msg where 
        a_split:"a = Receive sender pid msg" and 
        valid_pid:"pid \<in> qkdID ` \<Union> (bridgeIDs ` nodes)"
      by blast
    then have "a \<in> act network.ioa"
      unfolding actions_def asig_projections asig_of_def by auto
    then have net_trans:"net \<midarrow>a\<midarrow>network.ioa\<rightarrow> net'"
      using sys_trans by force
    then have net_eq:"net = net'"
      using 1 unfolding trans_of_def by auto
    have qkd_trans:"qkd \<midarrow>a\<midarrow>qkd_layer.ioa\<rightarrow> qkd'"
      using sys_trans assms(3) by force
    then show ?thesis
    proof (cases qkd)
      case (QKD gen sent)
      then show ?thesis
      proof (cases "\<exists>target. msg = GetKey pid target")
        case True
        then obtain target where msg_split:"msg = GetKey pid target"
          by blast
        then show ?thesis
        proof (cases "\<exists>keyID. keyID \<notin> fst ` ((snd ` gen) \<union> sent)")
          case True
          then obtain keyID0 where fresh0: "keyID0 \<notin> fst ` ((snd ` gen) \<union> sent)" 
            by blast
          have step: "qkd_layer_step (QKD gen sent) a qkd'"
          proof (rule ccontr)
            assume no_step: "\<not>qkd_layer_step (QKD gen sent) a qkd'"
            from qkd_trans QKD have "(QKD gen sent, a, qkd') \<in> qkd_layer.layer_trans"
              unfolding trans_of_def by simp
            then have stutter: "qkd' = QKD gen sent \<and> (\<forall>s'. \<not>qkd_layer_step (QKD gen sent) a s')"
              using no_step unfolding qkd_layer.layer_trans by auto
            have "qkd_layer_step (QKD gen sent) a (QKD (gen \<union> {(sender, keyID0, undefined)}) sent)"
              using qkd_layer_step.GetKey_Gen[OF fresh0, of sender pid target undefined]
              by (simp add: a_split msg_split True)
            then show False 
              using stutter by blast
          qed
          then obtain keyID keyVal where fresh: "keyID \<notin> fst ` ((snd ` gen) \<union> sent)"
                                     and qkd'_split: "qkd' = QKD (gen \<union> {(sender, keyID, keyVal)}) sent"
            by (cases rule: qkd_layer_step.cases; auto simp: a_split msg_split)
          show "P t"
            using assms(6)[OF valid_pid fresh _ net_eq QKD qkd'_split]
            by (simp add: a_split msg_split)
        next
          case False
          have "\<not>qkd_layer_step (QKD gen sent) a qkd'"
          proof (rule ccontr)
            assume "\<not> \<not>qkd_layer_step (QKD gen sent) a qkd'"
            then have "qkd_layer_step (QKD gen sent) a qkd'"
              by fast
            then show False
              apply (cases rule: qkd_layer_step.cases; auto simp: a_split msg_split)
              using False by blast
          qed
          then have "qkd = qkd'"
            using qkd_trans QKD unfolding trans_of_def qkd_layer.layer_trans by auto
          then show ?thesis
            using net_eq assms(2,4,5) by meson
        qed
      next
        case False
        then show ?thesis
        proof (cases "\<exists>target keyID. msg = GetKeyWithID pid target keyID")
          case True
          then obtain target keyID where msg_split:"msg = GetKeyWithID pid target keyID"
            by blast
          then show ?thesis
          proof (cases "\<exists>keyVal. (keyID, keyVal) \<in> sent")
            case True
            then obtain keyVal0 where valid_keyVal0: "(keyID, keyVal0) \<in> sent" 
              by blast
            have step: "qkd_layer_step (QKD gen sent) a qkd'"
            proof (rule ccontr)
              assume no_step: "\<not>qkd_layer_step (QKD gen sent) a qkd'"
              from qkd_trans QKD have "(QKD gen sent, a, qkd') \<in> qkd_layer.layer_trans"
                unfolding trans_of_def by simp
              then have stutter: "qkd' = QKD gen sent \<and> (\<forall>s'. \<not>qkd_layer_step (QKD gen sent) a s')"
                using no_step unfolding qkd_layer.layer_trans by auto
              have "qkd_layer_step (QKD gen sent) a (QKD (gen \<union> {(sender, keyID, keyVal0)}) (sent - {(keyID, keyVal0)}))"
                using qkd_layer_step.GetKeyWithID_Reserve[OF valid_keyVal0, of gen sender pid target]
                by (simp add: a_split msg_split)
              then show False 
                using stutter by blast
            qed
            then obtain keyVal where valid_keyVal: "(keyID, keyVal) \<in> sent"
                                and qkd'_split: "qkd' = QKD (gen \<union> {(sender, keyID, keyVal)}) (sent - {(keyID, keyVal)})"
              by (cases rule: qkd_layer_step.cases; auto simp: a_split msg_split)
            show "P t"
              using assms(7)[OF valid_pid valid_keyVal _ net_eq QKD qkd'_split]
              by (simp add: a_split msg_split)
          next
            case False
            have "\<not>qkd_layer_step (QKD gen sent) a qkd'"
            proof (rule ccontr)
              assume "\<not> \<not>qkd_layer_step (QKD gen sent) a qkd'"
              then have "qkd_layer_step (QKD gen sent) a qkd'"
                by fast
              then show False
                apply (cases rule: qkd_layer_step.cases; auto simp: a_split msg_split)
                using False by blast
            qed
            then have "qkd = qkd'"
              using qkd_trans QKD unfolding trans_of_def qkd_layer.layer_trans by auto
            then show ?thesis
              using net_eq assms(2,4,5) by meson
          qed
        next
          case False
          have "\<not>qkd_layer_step (QKD gen sent) a qkd'"
          proof
            assume "qkd_layer_step (QKD gen sent) a qkd'"
            then show False
              apply (cases rule: qkd_layer_step.cases)
              using a_split \<open>\<nexists>target. msg = GetKey pid target\<close> False by auto            
          qed
          then have "qkd = qkd'"
            using qkd_trans QKD unfolding trans_of_def qkd_layer.layer_trans by auto
          then show ?thesis
            using net_eq assms(2,4,5) by meson
        qed
      qed
    qed
  next
    case 2
    then obtain pid rcpt msg where 
        a_split:"a = Send pid rcpt msg" and 
        valid_pid:"pid \<in> qkdID ` \<Union> (bridgeIDs ` nodes)"
      by blast
    then have "a \<in> act network.ioa"
      unfolding actions_def asig_projections asig_of_def by auto
    then have net_trans:"net \<midarrow>a\<midarrow>network.ioa\<rightarrow> net'"
      using sys_trans by force
    then have net':"net' = net \<union> {(pid, rcpt, msg)}"
      using a_split unfolding trans_of_def by auto
    have qkd_trans:"qkd \<midarrow>a\<midarrow>qkd_layer.ioa\<rightarrow> qkd'"
      using sys_trans assms(3) by force
    show ?thesis
    proof (cases qkd)
      case (QKD gen sent)
      then consider "\<exists>keyID keyVal. msg = KeyResponse keyID keyVal"
        using qkd_trans
        unfolding a_split trans_of_def qkd_layer.layer_trans apply simp
        using qkd_layer_step.cases by blast
      then show ?thesis
      proof (cases)
        case 1
        then obtain keyID keyVal where msg_split:"msg = KeyResponse keyID keyVal"
          by presburger
        have in_gen:"(rcpt, keyID, keyVal) \<in> gen"
          using qkd_trans a_split msg_split QKD valid_pid apply simp
          unfolding trans_of_def qkd_layer.layer_trans apply auto
          using qkd_layer_step.cases by blast
        have qkd': "qkd' = QKD (gen - {(rcpt, keyID, keyVal)}) (sent \<union> {(keyID, keyVal)})"
          using qkd_trans a_split msg_split QKD valid_pid apply simp
          unfolding trans_of_def qkd_layer.layer_trans apply auto
          using qkd_layer_step.cases by force
        show ?thesis
          using assms(8)[OF valid_pid in_gen _ _ QKD qkd'] a_split msg_split net' by fast
      qed
    qed
  qed
qed

end

end