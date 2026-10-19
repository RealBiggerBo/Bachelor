theory QKD_System_Helpers_Kme_Trans_Elim
  imports QKD_System_Helpers_Trans_Elim QKD_System_ActsDisj
begin

inductive_cases kme_step_KMPostE:
  "kme_step enc dec (Kme store route saeToKme)
     (Receive sender rcpt (KMPost otherKme keyID keyVal)) st' sent"
inductive_cases kme_step_KMPutE:
  "kme_step enc dec (Kme store route saeToKme)
     (Receive sender rcpt (KMPut otherKme keyID None)) st' sent"
inductive_cases kme_step_GetKeyE:
  "kme_step enc dec (Kme store route saeToKme)
     (Receive sender rcpt (GetKey host slaveSae)) st' sent"
inductive_cases kme_step_KMPutReserveE:
  "kme_step enc dec (Kme store route saeToKme)
     (Receive sender rcpt (KMPut otherKme keyID (Some slaveSae))) st' sent"
inductive_cases kme_step_GetKeyWithIDE:
  "kme_step enc dec (Kme store route saeToKme)
     (Receive sender rcpt (GetKeyWithID host masterSae keyID)) st' sent"
inductive_cases kme_step_GetKeyWithID_RecE:
  "kme_step enc dec (Kme store route saeToKme)
     (Receive sender rcpt (KMGet masterSae keyID keyID2 slaveSae)) st' sent"

context QKD_Network
begin

lemma kmes_trans_elim [elim]:
  assumes "kmes \<midarrow>a\<midarrow>kmes.ioa\<rightarrow> kmes'"
  shows "(a \<in> act (kme.ioa n) \<and> n \<in> nodes \<longrightarrow> kmes n \<midarrow>a\<midarrow>kme.ioa n\<rightarrow> kmes' n) \<and> 
         (a \<notin> act (kme.ioa n) \<or> n \<notin> nodes \<longrightarrow> kmes n = kmes' n)"
  using set_ioa_trans_elim[OF assms] by blast

lemma kme_invariant_step[consumes 4, case_names 
    KMPost_NewKeyVal
    KMPut_Confirm
    GetKey
    KMPut_Reserve
    GetKey_Reserved
GetKeyWithID_IDFound
GetKeyWithID_IDNotFound
GetKeyWithID_IDNotFound_Reserved
KMGetKeyWithID_IDFound
KMGetKeyWithID_IDNotFound
KMGetKeyWithID_IDNotFound_Reserved
KMGetKeyWithID_IDNotFound_Return
GetKeyWithID_IDNotFound_Return
    Send]:
  assumes "reachable System.ioa s"
    and "P s"
    and "n \<in> nodes"
    and "a \<in> act (kme.ioa n)"
    and "s = (apps, kmes, bridges, qkd, net)"
    and "t = (apps, kmes', bridges, qkd, net')"
    and "\<And>sender otherKme keyID keyVal store route saeToKme msgs.
         \<lbrakk>a = Receive sender (kmeID n) (KMPost otherKme keyID keyVal); net = net';
          kmes n = IoaState (Kme store route saeToKme) msgs;
          kmes' = kmes(n := IoaState (Kme (keyStore_add store keyID (Some keyVal) otherKme) route saeToKme) 
          (msgs \<union> {(kmeID n, sender, OK), (kmeID n, otherKme, KMPut (kmeID n) keyID None)}))\<rbrakk> \<Longrightarrow> P t"
    and "\<And>sender otherKme keyID store route saeToKme msgs.
         \<lbrakk>a = Receive sender (kmeID n) (KMPut otherKme keyID None); net = net';
          kmes n = IoaState (Kme store route saeToKme) msgs;
          kmes' = kmes(n := IoaState (Kme (keyStore_confirm store keyID otherKme) route saeToKme) 
          (msgs \<union> {(kmeID n, sender, OK)}))\<rbrakk> \<Longrightarrow> P t"
    and "\<And>sender host slaveSae store route saeToKme msgs keyID val.
         \<lbrakk>a = Receive sender (kmeID n) (GetKey host slaveSae); net = net';
          store keyID = Some (Some val, route slaveSae, True, None);
          kmes n = IoaState (Kme store route saeToKme) msgs;
          kmes' = kmes(n := IoaState (KmeWaitReserve keyID sender store route saeToKme) 
          (msgs \<union> {(kmeID n, route slaveSae, KMPut (kmeID n) keyID (Some slaveSae))}))\<rbrakk> \<Longrightarrow> P t"
    and "\<And>sender otherKme slaveSae store route saeToKme msgs keyID.
         \<lbrakk>a = Receive sender (kmeID n) (KMPut otherKme keyID (Some slaveSae)); net = net';
          kmes n = IoaState (Kme store route saeToKme) msgs;
          kmes' = kmes(n := IoaState (Kme (keyStore_reserve store keyID slaveSae) route saeToKme) 
          (msgs \<union> {(kmeID n, otherKme, OK)}))\<rbrakk> \<Longrightarrow> P t"
    and "\<And>sender store keyID val conf res saeID route saeToKme msgs.
         \<lbrakk>a = Receive sender (kmeID n) OK; net = net';
          store keyID = Some (Some val, sender, conf, res);
          kmes n = IoaState (KmeWaitReserve keyID saeID store route saeToKme) msgs;
          kmes' = kmes(n := IoaState (Kme (keyStore_remove store keyID) route saeToKme) 
          (msgs \<union> {(kmeID n, saeID, KeyResponse keyID val)}))\<rbrakk> \<Longrightarrow> P t"
    and "\<And>sender host store keyID val saeToKme masterSae route saeToKme msgs.
         \<lbrakk>a = Receive sender (kmeID n) (GetKeyWithID host masterSae keyID); net = net';
          store keyID = Some (Some val, saeToKme masterSae, True, Some sender);
          kmes n = IoaState (Kme store route saeToKme) msgs;
          kmes' = kmes(n := IoaState (Kme (keyStore_remove store keyID) route saeToKme) 
          (msgs \<union> {(kmeID n, sender, KeyResponse keyID val)}))\<rbrakk> \<Longrightarrow> P t"
    and "\<And>sender host masterSae keyID store route nextKme keyID2 val2 saeToKme msgs val.
         \<lbrakk>a = Receive sender (kmeID n) (GetKeyWithID host masterSae keyID); net = net';
          store keyID = None;
          route masterSae = nextKme;
          store keyID2 = Some (Some val2, nextKme, True, None);
          kmes n = IoaState (Kme store route saeToKme) msgs;
          kmes' = kmes(n := IoaState (KmeWaitHop masterSae sender nextKme keyID keyID2 store route saeToKme) 
          (msgs \<union> {(kmeID n, nextKme, KMPut (kmeID n) keyID2 (Some (kmeID n)))}))\<rbrakk> \<Longrightarrow> P t"
    and "\<And>nextKme masterSae slaveSae keyID keyID2 store route saeToKme msgs.
         \<lbrakk>a = Receive nextKme (kmeID n) OK; net = net';
          kmes n = IoaState (KmeWaitHop masterSae slaveSae nextKme keyID keyID2 store route saeToKme) msgs;
          kmes' = kmes(n := IoaState (KmeWaitHop masterSae slaveSae nextKme keyID keyID2 store route saeToKme) 
          (msgs \<union> {(kmeID n, nextKme, KMGet masterSae keyID keyID2 slaveSae)}))\<rbrakk> \<Longrightarrow> P t"
    and "\<And>nextKme masterSae keyID keyID2 slaveSae store route saeToKme msgs sender val val2.
         \<lbrakk>a = Receive nextKme (kmeID n) (KMGet masterSae keyID keyID2 slaveSae); net = net';
          store keyID = Some (Some val, saeToKme masterSae, True, None);
          store keyID2 = Some (Some val2, sender, True, Some sender);
          kmes n = IoaState (Kme store route saeToKme) msgs;
          kmes' = kmes(n := IoaState (Kme (keyStore_remove (keyStore_remove store keyID) keyID2) route saeToKme) 
          (msgs \<union> {(kmeID n, sender, KeyResponse keyID (enc val val2))}))\<rbrakk> \<Longrightarrow> P t"
    and "\<And>nextKme masterSae keyID keyID2 slaveSae store val2 sender route keyID3 val3 saeToKme msgs.
         \<lbrakk>a = Receive sender (kmeID n) (KMGet masterSae keyID keyID2 slaveSae); net = net';
          store keyID = None;
          store keyID2 = Some (Some val2, sender, True, Some sender);
          route masterSae = nextKme;
          store keyID3 = Some (Some val3, nextKme, True, None);
          kmes n = IoaState (Kme store route saeToKme) msgs;
          kmes' = kmes(n := IoaState (KmeWaitHopRec keyID3 masterSae sender nextKme keyID keyID2 store route saeToKme) 
          (msgs \<union> {(kmeID n, nextKme, KMPut (kmeID n) keyID3 (Some (kmeID n)))}))\<rbrakk> \<Longrightarrow> P t"
    and "\<And>nextKme masterSae keyID keyID2 slaveSae store sender route keyID3 saeToKme msgs.
         \<lbrakk>a = Receive nextKme (kmeID n) (KMGet masterSae keyID keyID2 slaveSae); net = net';
          kmes n = IoaState (KmeWaitHopRec keyID3 masterSae sender nextKme keyID keyID2 store route saeToKme) msgs;
          kmes' = kmes(n := IoaState (KmeWaitHopRec keyID3 masterSae sender nextKme keyID keyID2 store route saeToKme) 
          (msgs \<union> {(kmeID n, nextKme, KMGet masterSae keyID keyID3 slaveSae)}))\<rbrakk> \<Longrightarrow> P t"
    and "\<And>nextKme keyID keyVal' store keyID2 val2 sender keyID3 val3 masterSae route saeToKme msgs slaveSae.
         \<lbrakk>a = Receive nextKme (kmeID n) (KeyResponse keyID keyVal'); net = net';
          store keyID2 = Some (Some val2, sender, True, Some sender);
          store keyID3 = Some (Some val3, nextKme, True, None);
          kmes n = IoaState (KmeWaitHopRec keyID3 masterSae sender nextKme keyID keyID2 store route saeToKme) msgs;
          kmes' = kmes(n := IoaState (KmeWaitHopRec keyID3 masterSae sender nextKme keyID keyID2 store route saeToKme) 
          (msgs \<union> {(kmeID n, sender, KeyResponse keyID (enc (dec keyVal' val3) val2))}))\<rbrakk> \<Longrightarrow> P t"
    and "\<And>nextKme keyID keyVal' store keyID2 val2 masterSae sender keyID3 val3 masterSae route saeToKme msgs slaveSae.
         \<lbrakk>a = Receive nextKme (kmeID n) (KeyResponse keyID keyVal'); net = net';
          store keyID2 = Some (Some val2, nextKme, True, None);
          kmes n = IoaState (KmeWaitHop masterSae sender nextKme keyID keyID2 store route saeToKme) msgs;
          kmes' = kmes(n := IoaState (Kme (keyStore_remove store keyID2) route saeToKme) 
          (msgs \<union> {(kmeID n, sender, KeyResponse keyID (dec keyVal' val2))}))\<rbrakk> \<Longrightarrow> P t"
    and "\<And>msgs rcpt msg appState.
         \<lbrakk>a = Send (kmeID n) rcpt msg; net' = net \<union> {(kmeID n, rcpt, msg)};
          (kmeID n, rcpt, msg) \<in> msgs;
          kmes n = IoaState appState msgs;
          kmes' = kmes(n := IoaState appState (msgs - {(kmeID n, rcpt, msg)}))\<rbrakk> \<Longrightarrow> P t"
  shows "s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t \<longrightarrow> P t"
proof
  assume sat_trans:"s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t"
  note sys_trans = System_trans_elim[OF sat_trans assms(5,6)]
  have kmes_trans:"kmes \<midarrow>a\<midarrow>kmes.ioa\<rightarrow> kmes'"
    using sys_trans assms(3,4) unfolding actions_of_set_ioa by blast
  then have kme_node_trans: "kmes n \<midarrow>a\<midarrow>kme.ioa n\<rightarrow> kmes' n"
    using assms(3,4) kmes_trans_elim by blast
  moreover have other_kmes_eq: "\<And>n'. \<lbrakk>n' \<in> nodes; n' \<noteq> n\<rbrakk> \<Longrightarrow> kmes n' = kmes' n'"
    using kmes_trans_elim[OF kmes_trans] actsDisj_kme_kme assms(3,4) by blast
  moreover have "\<And>n'. \<lbrakk>n' \<notin> nodes\<rbrakk> \<Longrightarrow> kmes n' = kmes' n'"
    using kmes_trans unfolding trans_of_set_ioa by simp
  ultimately have kmes': "kmes' = kmes (n := kmes' n)"
    by fastforce
  consider "\<exists>sender msg. a = Receive sender (kmeID n) msg" | "\<exists>rcpt msg. a = Send (kmeID n) rcpt msg"
    using assms(4) unfolding actions_def asig_projections asig_of_def by auto
  then show "P t"
  proof cases
    case 1
    then have "a \<in> act network.ioa"
      unfolding actions_def asig_projections asig_of_def by force
    then have "net \<midarrow>a\<midarrow>network.ioa\<rightarrow> net'"
      using sys_trans by meson
    then have net_eq:"net = net'"
      using 1 unfolding trans_of_def by auto
    obtain sender msg where a_split:"a = Receive sender (kmeID n) msg"
      using 1 by presburger
    then show ?thesis
    proof (cases "kmes n")
      case (IoaState state msgs)
      then show ?thesis
      proof (cases state)
        case (Kme store route saeToKme)
        then show ?thesis
        proof (cases "\<exists>otherKme keyID keyVal. msg = KMPost otherKme keyID keyVal")
          case True
          then obtain otherKme keyID keyVal where msg_split:"msg = KMPost otherKme keyID keyVal"
            by blast
          then have "kmes' n = IoaState (Kme (keyStore_add store keyID (Some keyVal) otherKme) route saeToKme) 
                                        (msgs \<union> {(kmeID n, sender, OK), (kmeID n, otherKme, KMPut (kmeID n) keyID None)})"
            using a_split assms(4) kme_node_trans IoaState Kme unfolding trans_of_def apply simp
            unfolding actions_def asig_projections asig_of_def apply simp
            apply (auto elim: kme_step_KMPostE)
            using KMPost_NewKeyVal by fast+
          then show ?thesis
            using assms(7)[OF _ net_eq] IoaState kmes' msg_split a_split Kme by presburger
        next
          case False
          then show ?thesis
          proof (cases "\<exists>otherKme keyID. msg = KMPut otherKme keyID None")
            case True
            then obtain otherKme keyID where msg_split:"msg = KMPut otherKme keyID None"
              by blast
            then have "kmes' n = IoaState (Kme (keyStore_confirm store keyID otherKme) route saeToKme)
                                        (msgs \<union> {(kmeID n, sender, OK)})"
              using a_split assms(4) kme_node_trans IoaState Kme unfolding trans_of_def apply simp
              unfolding actions_def asig_projections asig_of_def apply simp
              apply (auto elim: kme_step_KMPutE)
              using KMPut_Confirm by fast+
            then show ?thesis
              using assms(8)[OF _ net_eq] IoaState kmes' msg_split a_split Kme by presburger
          next
            case False
            then show ?thesis
            proof (cases "\<exists>host slaveSae. msg = GetKey host slaveSae")
              case True
              then obtain host slaveSae where msg_split:"msg = GetKey host slaveSae"
                by blast
              then show ?thesis
              proof (cases "\<exists>keyID val. store keyID = Some (Some val, route slaveSae, True, None)")
                case True
                then obtain keyID0 val0 where prem0: "store keyID0 = Some (Some val0, route slaveSae, True, None)"
                  by blast
                then obtain keyID val where prem: "store keyID = Some (Some val, route slaveSae, True, None)"
                                      and kn: "kmes' n = IoaState (KmeWaitReserve keyID sender store route saeToKme)
                                      (msgs \<union> {(kmeID n, route slaveSae, KMPut (kmeID n) keyID (Some slaveSae))})"
                  using kme_node_trans Kme msg_split a_split IoaState unfolding trans_of_def apply auto
                  apply (smt (verit) Un_commute image_empty image_insert insert_is_Un ioa_state.inject kme_step_GetKeyE)
                  by (meson GetKey)
                show ?thesis
                  using assms(9)[OF _ net_eq] IoaState kmes' kn msg_split a_split Kme prem
                  by metis
              next
                case False
                then have "kmes' n = kmes n"
                  using kme_node_trans Kme msg_split a_split IoaState unfolding trans_of_def apply auto
                  using kme_step.cases by (smt (verit, del_insts) kme_step_GetKeyE)+
                then show ?thesis
                  using kmes' assms(2,5,6) net_eq by force
              qed
            next
              case False
              then show ?thesis
              proof (cases "\<exists>otherKme keyID slaveSae. msg = KMPut otherKme keyID (Some slaveSae)")
                case True
                then obtain otherKme keyID slaveSae where msg_split:"msg = KMPut otherKme keyID (Some slaveSae)"
                  by blast
                then have "kmes' n = IoaState (Kme (keyStore_reserve store keyID slaveSae) route saeToKme)
                                              (msgs \<union> {(kmeID n, otherKme, OK)})"
                  using a_split assms(4) kme_node_trans IoaState Kme unfolding trans_of_def apply simp
                  unfolding actions_def asig_projections asig_of_def apply simp
                  apply (auto elim: kme_step_KMPutReserveE)
                  using KMPut_Reserve by fast+
                then show ?thesis
                  using assms(10)[OF _ net_eq] IoaState kmes' msg_split a_split Kme by presburger
              next
                case False
                then show ?thesis
                proof (cases "\<exists>host masterSae keyID. msg = GetKeyWithID host masterSae keyID")
                  case True
                  then obtain host masterSae keyID where msg_split: "msg = GetKeyWithID host masterSae keyID"
                    by blast
                  then show ?thesis
                  proof (cases "\<exists>val. store keyID = Some (Some val, saeToKme masterSae, True, Some sender)")
                    case True
                    then obtain val where store_keyID: "store keyID = Some (Some val, saeToKme masterSae, True, Some sender)"
                      by blast
                    then have "kmes' n = IoaState (Kme (keyStore_remove store keyID) route saeToKme)
                                                  (msgs \<union> {(kmeID n, sender, KeyResponse keyID val)})"
                      using a_split assms(4) kme_node_trans IoaState Kme msg_split unfolding trans_of_def apply simp
                      unfolding actions_def asig_projections asig_of_def apply simp
                      apply (auto elim: kme_step_GetKeyWithIDE)
                      using GetKeyWithID_IDFound by fast+
                    then show ?thesis
                      using assms(12)[OF _ net_eq] IoaState kmes' msg_split a_split Kme store_keyID by presburger
                  next
                    case False
                    then show ?thesis
                    proof (cases "store keyID = None")
                      case True
                      obtain nextKme where nxtKme: "nextKme = route masterSae"
                        by simp
                      then show ?thesis
                      proof (cases "\<exists>keyID2 val2. store keyID2 = Some (Some val2, nextKme, True, None)")
                        case True
                        then obtain keyID20 val20 where prem0: "store keyID20 = Some (Some val20, nextKme, True, None)"
                          by blast
                        then obtain keyID2 val2 where prem: "store keyID2 = Some (Some val2, nextKme, True, None)"
                                                and kn: "kmes' n = IoaState (KmeWaitHop masterSae sender nextKme keyID keyID2 store route saeToKme)
                                                        (msgs \<union> {(kmeID n, nextKme, KMPut (kmeID n) keyID2 (Some (kmeID n)))})"
                          using kme_node_trans Kme msg_split a_split IoaState nxtKme \<open>store keyID = None\<close> unfolding trans_of_def apply auto
                          using Un_commute image_empty image_insert insert_is_Un ioa_state.inject kme_step_GetKeyWithIDE
                           apply (smt (verit, ccfv_SIG) not_None_eq)
                          by (meson GetKeyWithID_IDNotFound)
                        show ?thesis
                          using assms(13)[OF _ net_eq] IoaState kmes' kn msg_split a_split Kme prem nxtKme \<open>store keyID = None\<close>
                          by metis
                      next
                        case False
                        then have "kmes' n = kmes n"
                          using kme_node_trans Kme msg_split a_split IoaState nxtKme \<open>store keyID = None\<close> 
                          unfolding trans_of_def apply auto
                          by (smt (verit) kme_step_GetKeyWithIDE option.discI)+
                        then show ?thesis
                          using kmes' assms(2,5,6) net_eq by force
                      qed
                    next
                      case False
                      then have "kmes' n = kmes n"
                        apply(cases "\<exists>st' sent. kme_step enc dec (Kme store route saeToKme) (Receive sender (kmeID n) (GetKeyWithID host masterSae keyID)) st' sent")
                        using kme_node_trans Kme msg_split a_split IoaState 
                        using \<open>\<nexists>val. store keyID = Some (Some val, saeToKme masterSae, True, Some sender)\<close>
                        unfolding trans_of_def apply auto
                        using kme_step_GetKeyWithIDE[of enc dec store route saeToKme sender "kmeID n" host masterSae keyID]
                        by auto
                      then show ?thesis
                        using kmes' assms(2,5,6) net_eq by force
                    qed
                  qed
                next
                  case False
                  then show ?thesis
                  proof (cases "\<exists>masterSae keyID keyID2 slaveSae. msg = KMGet masterSae keyID keyID2 slaveSae")
                    case True
                    (*COPY PASTE*)
                    then obtain masterSae keyID keyID2 slaveSae where msg_split: "msg = KMGet masterSae keyID keyID2 slaveSae"
                      by blast
                    then show ?thesis
                    proof (cases "\<exists>val. store keyID = Some (Some val, saeToKme masterSae, True, None)")
                      case True
                      then obtain val where store_keyID: "store keyID = Some (Some val, saeToKme masterSae, True, None)"
                        by blast
                      then show ?thesis
                      proof (cases "\<exists>val2. store keyID2 = Some (Some val2, sender, True, Some sender)")
                        case True
                        then obtain val2 where store_keyID2: "store keyID2 = Some (Some val2, sender, True, Some sender)"
                          by blast
                        then have "kmes' n = IoaState (Kme (keyStore_remove (keyStore_remove store keyID) keyID2) route saeToKme)
                                                  (msgs \<union> {(kmeID n, sender, KeyResponse keyID (enc val val2))})"
                          using a_split assms(4) kme_node_trans IoaState Kme msg_split store_keyID unfolding trans_of_def apply simp
                          unfolding actions_def asig_projections asig_of_def apply simp
                          apply (auto elim: kme_step_GetKeyWithID_RecE)
                          using KMGetKeyWithID_IDFound by meson+
                        then show ?thesis
                          using assms(15)[OF _ net_eq] IoaState kmes' msg_split a_split Kme store_keyID store_keyID2
                          by metis
                      next
                        case False
                        then have "kmes' n = kmes n"
                          using kme_node_trans Kme msg_split a_split IoaState 
                          unfolding trans_of_def apply auto
                          by (smt (verit) kme_step_GetKeyWithID_RecE option.discI)+
                        then show ?thesis
                          using kmes' assms(2,5,6) net_eq by force
                      qed
                    next
                      case False
                      then show ?thesis
                      proof (cases "store keyID = None")
                        case True
                        obtain nextKme where nxtKme: "nextKme = route masterSae"
                          by simp
                        then show ?thesis
                        proof (cases "\<exists>val2. store keyID2 = Some (Some val2, sender, True, Some sender)")
                          case True
                          then obtain val2 where val2_split:"store keyID2 = Some (Some val2, sender, True, Some sender)"
                            by blast
                          then show ?thesis
                          proof (cases "\<exists>keyID3 val3. store keyID3 = Some (Some val3, nextKme, True, None)")
                            case True
                            then obtain keyID30 val30 where prem:"store keyID30 = Some (Some val30, nextKme, True, None)"
                              by blast
                            then obtain keyID3 val3 where prem: "store keyID3 = Some (Some val3, nextKme, True, None)"
                                                and kn: "kmes' n = IoaState (KmeWaitHopRec keyID3 masterSae sender nextKme keyID keyID2 store route saeToKme)
                                                        (msgs \<union> {(kmeID n, nextKme, KMPut (kmeID n) keyID3 (Some (kmeID n)))})"
                              using kme_node_trans Kme msg_split a_split IoaState nxtKme val2_split \<open>store keyID = None\<close> 
                              unfolding trans_of_def apply auto
                              using Un_commute image_empty image_insert insert_is_Un ioa_state.inject kme_step_GetKeyWithID_RecE
                               apply (smt (verit, ccfv_SIG) not_None_eq)
                              using KMGetKeyWithID_IDNotFound by meson
                            then show ?thesis
                              using assms(16)[OF _ net_eq] IoaState kmes' kn msg_split a_split Kme prem nxtKme val2_split \<open>store keyID = None\<close>
                              by force
                          next
                            case False
                            then have "kmes' n = kmes n"
                              using kme_node_trans Kme msg_split a_split IoaState nxtKme \<open>store keyID = None\<close> 
                              unfolding trans_of_def apply auto
                              by (smt (verit) kme_step_GetKeyWithID_RecE option.discI)+
                            then show ?thesis
                              using kmes' assms(2,5,6) net_eq by force
                          qed
                        next
                          case False
                          then have "kmes' n = kmes n"
                            using kme_node_trans Kme msg_split a_split IoaState 
                            unfolding trans_of_def apply auto
                            by (smt (verit) kme_step_GetKeyWithID_RecE option.discI)+
                          then show ?thesis
                            using kmes' assms(2,5,6) net_eq by force
                        qed
                      next
                        case False
                        then have "kmes' n = kmes n"
                          using kme_node_trans Kme msg_split a_split IoaState
                          unfolding trans_of_def apply auto
                          using False \<open>\<nexists>val. store keyID = Some (Some val, saeToKme masterSae, True, None)\<close> kme_step_GetKeyWithID_RecE 
                           by (fastforce,meson)
                        then show ?thesis
                          using kmes' assms(2,5,6) net_eq by force
                      qed
                    qed
                  next
                    case False
                    have "\<forall>st' sent. \<not>kme_step enc dec state a st' sent"
                      using a_split kme_step.cases Kme
                        \<open>\<nexists>otherKme keyID keyVal. msg = KMPost otherKme keyID keyVal\<close>
                        \<open>\<nexists>otherKme keyID. msg = KMPut otherKme keyID None\<close>
                        \<open>\<nexists>host slaveSae. msg = GetKey host slaveSae\<close>
                        \<open>\<nexists>otherKme keyID slaveSae. msg = KMPut otherKme keyID (Some slaveSae)\<close>
                        \<open>\<nexists>host masterSae keyID. msg = GetKeyWithID host masterSae keyID\<close>
                        \<open>\<nexists>masterSae keyID keyID2 slaveSae. msg = KMGet masterSae keyID keyID2 slaveSae\<close>
                      apply auto
                      by (cases rule: kme_step.cases) auto
                    then have "kmes' n = kmes n"
                      using kme_node_trans Kme a_split IoaState unfolding trans_of_def by simp
                    then show ?thesis
                      using kmes' assms(2,5,6) net_eq by force
                  qed
                qed
              qed
            qed
          qed
        qed
      next
        case (KmeWaitReserve keyID saeID store route saeToKme)
        then show ?thesis sorry
      next
        case (KmeWaitHop masterSae slaveSae nextKme keyID encryptionKeyID store route saeToKme)
        then show ?thesis sorry
      next
        case (KmeWaitHopRec recEncryptionKeyID masterSae slaveSae nextKme keyID encryptionKeyID store route saeToKme)
        then show ?thesis sorry
      qed
    qed
  next
    case 2
    then have "a \<in> act network.ioa"
      unfolding actions_def asig_projections asig_of_def by auto
    then have net_trans:"net \<midarrow>a\<midarrow>network.ioa\<rightarrow> net'"
      using sys_trans by force
    obtain rcpt msg where a_split:"a = Send (kmeID n) rcpt msg"
      using 2 by blast
    then have net':"net' = net \<union> {(kmeID n, rcpt, msg)}"
      using net_trans unfolding trans_of_def by auto
    then show ?thesis
    proof (cases "kmes n")
      case (IoaState state msgs)
      then have "(kmeID n, rcpt, msg) \<in> msgs"
        using kme_node_trans a_split unfolding trans_of_def by simp
      moreover have "kmes' n = IoaState state (msgs - {(kmeID n, rcpt, msg)})"
        using calculation kme_node_trans a_split IoaState unfolding trans_of_def by simp
      ultimately show ?thesis
        using assms(20) a_split net' IoaState kmes' by presburger
    qed
  qed
qed

end

end