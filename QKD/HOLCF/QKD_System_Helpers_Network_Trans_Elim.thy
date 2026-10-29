theory QKD_System_Helpers_Network_Trans_Elim
  imports QKD_System_Helpers_Trans_Elim QKD_System_ActsDisj
begin

context QKD_Network
begin

lemma network_invariant_step[consumes 9, case_names
    Ext_Receive
    Ext_Send]:
  assumes "reachable System.ioa s"
    and "P s"
    and "a \<notin> act apps.ioa"
    and "a \<notin> act kmes.ioa"
    and "a \<notin> act bridges.ioa"
    and "a \<notin> act qkd_layer.ioa"
    and "a \<in> act network.ioa"
    and "s = (apps, kmes, bridges, qkd, net)"
    and "t = (apps, kmes, bridges, qkd, net')"
    and "\<And>sender rcpt msg all.
         \<lbrakk>a = Receive sender rcpt msg;
          all = (appID ` nodes) \<union> (kmeID ` nodes) \<union> \<Union>(bridgeIDs ` nodes) \<union> qkdID ` (\<Union>(bridgeIDs ` nodes));
          rcpt \<notin> all;
          net' = rmv_msg net sender rcpt msg\<rbrakk> \<Longrightarrow> P t"
    and "\<And>sender rcpt msg all.
         \<lbrakk>a = Send sender rcpt msg;
          all = (appID ` nodes) \<union> (kmeID ` nodes) \<union> \<Union>(bridgeIDs ` nodes) \<union> qkdID ` (\<Union>(bridgeIDs ` nodes));
          sender \<notin> all;
          net' = add_msg net sender rcpt msg\<rbrakk> \<Longrightarrow> P t"
  shows "s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t \<longrightarrow> P t"
proof
  let ?all = "(appID ` nodes) \<union> (kmeID ` nodes) \<union> \<Union>(bridgeIDs ` nodes) \<union> qkdID ` (\<Union>(bridgeIDs ` nodes))"
  assume sat_trans:"s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t"
  then have trans_net:"net \<midarrow>a\<midarrow>network.ioa\<rightarrow> net'"
    using System_trans_elim[OF sat_trans assms(8,9)] assms(7) by force
  have "a \<in> act System.ioa"
    by (smt (verit) assms(7) par_actR)
  then have "a \<in> {Send sender rcpt msg | sender rcpt msg. sender \<notin> ?all} \<union>
                 {Receive sender rcpt msg | sender rcpt msg. rcpt \<notin> ?all}"
    using acts_only_netw assms(3-6) by blast
  then consider "\<exists>sender rcpt msg. a = Send sender rcpt msg \<and> sender \<notin> ?all" | "\<exists>sender rcpt msg. a = Receive sender rcpt msg \<and> rcpt \<notin> ?all"
    by blast
  then show "P t"
  proof cases
    case 1
    then obtain sender rcpt msg where "a = Send sender rcpt msg"
                                and "sender \<notin> ?all"
      by metis
    moreover have "net' = add_msg net sender rcpt msg"
      using trans_net calculation(1) unfolding trans_of_def by force
    ultimately show ?thesis
      using assms(11) by blast
  next
    case 2
    then obtain sender rcpt msg where "a = Receive sender rcpt msg"
                                and "rcpt \<notin> ?all"
      by metis
    moreover have "net' = rmv_msg net sender rcpt msg"
      using trans_net calculation(1) unfolding trans_of_def by force
    ultimately show ?thesis
      using assms(10) by blast
  qed
qed

end

end