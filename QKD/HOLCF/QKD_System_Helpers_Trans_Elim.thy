theory QKD_System_Helpers_Trans_Elim
  imports QKD_System_Def
begin

context QKD_Network
begin

lemma System_trans_elim [elim]:
  assumes "s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t"
      and "s = (apps, kmes, bridges, qkd, net)"
      and "t = (apps', kmes', bridges', qkd', net')"
  shows "(a \<in> act apps.ioa \<longrightarrow> apps \<midarrow>a\<midarrow>apps.ioa\<rightarrow> apps') \<and>
         (a \<notin> act apps.ioa \<longrightarrow> apps = apps') \<and>
         (a \<in> act kmes.ioa \<longrightarrow> kmes \<midarrow>a\<midarrow>kmes.ioa\<rightarrow> kmes') \<and>
         (a \<notin> act kmes.ioa \<longrightarrow> kmes = kmes') \<and>
         (a \<in> act bridges.ioa \<longrightarrow> bridges \<midarrow>a\<midarrow>bridges.ioa\<rightarrow> bridges') \<and>
         (a \<notin> act bridges.ioa \<longrightarrow> bridges = bridges') \<and>
         (a \<in> act qkd_layer.ioa \<longrightarrow> qkd \<midarrow>a\<midarrow>qkd_layer.ioa\<rightarrow> qkd') \<and>
         (a \<notin> act qkd_layer.ioa \<longrightarrow> qkd = qkd') \<and>
         (a \<in> act network.ioa \<longrightarrow> net \<midarrow>a\<midarrow>network.ioa\<rightarrow> net') \<and>
         (a \<notin> act network.ioa \<longrightarrow> net = net')"
proof -
  let ?a = "a \<in> act apps.ioa \<longrightarrow> apps \<midarrow>a\<midarrow>apps.ioa\<rightarrow> apps'"
  let ?b = "a \<notin> act apps.ioa \<longrightarrow> apps = apps'"
  let ?c = "a \<in> act kmes_bridges_qkd_layer_network.ioa \<longrightarrow> (kmes, bridges, qkd, net) \<midarrow>a\<midarrow>kmes_bridges_qkd_layer_network.ioa\<rightarrow> (kmes', bridges', qkd', net')"
  let ?d = "a \<notin> act kmes_bridges_qkd_layer_network.ioa \<longrightarrow> (kmes, bridges, qkd, net) = (kmes', bridges', qkd', net')"
  have ABCD:"?a \<and> ?b \<and> ?c \<and> ?d"
    using assms(1) par_trans_elim[of s a t apps.ioa kmes_bridges_qkd_layer_network.ioa]
    by (simp only: assms(2,3) snd_conv fst_conv; fastforce)
  moreover have "(a \<in> act kmes.ioa \<longrightarrow> kmes \<midarrow>a\<midarrow>kmes.ioa\<rightarrow> kmes') \<and>
         (a \<notin> act kmes.ioa \<longrightarrow> kmes = kmes') \<and>
         (a \<in> act bridges.ioa \<longrightarrow> bridges \<midarrow>a\<midarrow>bridges.ioa\<rightarrow> bridges') \<and>
         (a \<notin> act bridges.ioa \<longrightarrow> bridges = bridges') \<and>
         (a \<in> act qkd_layer.ioa \<longrightarrow> qkd \<midarrow>a\<midarrow>qkd_layer.ioa\<rightarrow> qkd') \<and>
         (a \<notin> act qkd_layer.ioa \<longrightarrow> qkd = qkd') \<and>
         (a \<in> act network.ioa \<longrightarrow> net \<midarrow>a\<midarrow>network.ioa\<rightarrow> net') \<and>
         (a \<notin> act network.ioa \<longrightarrow> net = net')"
  proof (cases "a \<in> act kmes_bridges_qkd_layer_network.ioa")
    case True
    let ?a = "a \<in> act kmes.ioa \<longrightarrow> kmes \<midarrow>a\<midarrow>kmes.ioa\<rightarrow> kmes'"
    let ?b = "a \<notin> act kmes.ioa \<longrightarrow> kmes = kmes'"
    let ?c = "a \<in> act bridges_qkd_layer_network.ioa \<longrightarrow> (bridges, qkd, net) \<midarrow>a\<midarrow>bridges_qkd_layer_network.ioa\<rightarrow> (bridges', qkd', net')"
    let ?d = "a \<notin> act bridges_qkd_layer_network.ioa \<longrightarrow> (bridges, qkd, net) = (bridges', qkd', net')"
    have trans:"(kmes, bridges, qkd, net) \<midarrow>a\<midarrow>kmes_bridges_qkd_layer_network.ioa\<rightarrow> (kmes', bridges', qkd', net')"
      using True ABCD by fast
    have ABCD':"?a \<and> ?b \<and> ?c \<and> ?d"
      using par_trans_elim[OF trans] 
      by (simp only: fst_conv snd_conv)
    moreover have "(a \<in> act bridges.ioa \<longrightarrow> bridges \<midarrow>a\<midarrow>bridges.ioa\<rightarrow> bridges') \<and>
                   (a \<notin> act bridges.ioa \<longrightarrow> bridges = bridges') \<and>
                   (a \<in> act qkd_layer.ioa \<longrightarrow> qkd \<midarrow>a\<midarrow>qkd_layer.ioa\<rightarrow> qkd') \<and>
                   (a \<notin> act qkd_layer.ioa \<longrightarrow> qkd = qkd') \<and>
                   (a \<in> act network.ioa \<longrightarrow> net \<midarrow>a\<midarrow>network.ioa\<rightarrow> net') \<and>
                   (a \<notin> act network.ioa \<longrightarrow> net = net')"
    proof (cases "a \<in> act bridges_qkd_layer_network.ioa")
      case True
      let ?a = "a \<in> act bridges.ioa \<longrightarrow> bridges \<midarrow>a\<midarrow>bridges.ioa\<rightarrow> bridges'"
      let ?b = "a \<notin> act bridges.ioa \<longrightarrow> bridges = bridges'"
      let ?c = "a \<in> act qkd_layer_network.ioa \<longrightarrow> (qkd, net) \<midarrow>a\<midarrow>qkd_layer_network.ioa\<rightarrow> (qkd', net')"
      let ?d = "a \<notin> act qkd_layer_network.ioa \<longrightarrow> (qkd, net) = (qkd', net')"
      have trans':"(bridges, qkd, net) \<midarrow>a\<midarrow>bridges_qkd_layer_network.ioa\<rightarrow> (bridges', qkd', net')"
        using True ABCD' by fastforce
      have ABCD'':"?a \<and> ?b \<and> ?c \<and> ?d"
        using par_trans_elim[OF trans']
        by (simp only: fst_conv snd_conv)
      moreover have "(a \<in> act qkd_layer.ioa \<longrightarrow> qkd \<midarrow>a\<midarrow>qkd_layer.ioa\<rightarrow> qkd') \<and>
                     (a \<notin> act qkd_layer.ioa \<longrightarrow> qkd = qkd') \<and>
                     (a \<in> act network.ioa \<longrightarrow> net \<midarrow>a\<midarrow>network.ioa\<rightarrow> net') \<and>
                     (a \<notin> act network.ioa \<longrightarrow> net = net')"
      proof (cases "a \<in> act qkd_layer_network.ioa")
        case True
        let ?a = "a \<in> act qkd_layer.ioa \<longrightarrow> qkd \<midarrow>a\<midarrow>qkd_layer.ioa\<rightarrow> qkd'"
        let ?b = "a \<notin> act qkd_layer.ioa \<longrightarrow> qkd = qkd'"
        let ?c = "a \<in> act network.ioa \<longrightarrow> net \<midarrow>a\<midarrow>network.ioa\<rightarrow> net'"
        let ?d = "a \<notin> act network.ioa \<longrightarrow> net = net'"
        have trans'':"(qkd, net) \<midarrow>a\<midarrow>qkd_layer_network.ioa\<rightarrow> (qkd', net')"
          using True ABCD'' by fastforce
        have "?a \<and> ?b \<and> ?c \<and> ?d"
          using par_trans_elim[OF trans'']
          by (simp only: fst_conv snd_conv)
        then show ?thesis
          by meson
      next
        case False
        then have "a \<notin> act qkd_layer.ioa \<and> a \<notin> act network.ioa"
          unfolding actions_of_par by fastforce
        then show ?thesis
          using ABCD'' False by fastforce
      qed
      ultimately show ?thesis 
        by force
    next
      case False
      then have "a \<notin> act bridges.ioa \<and> a \<notin> act qkd_layer.ioa \<and> a \<notin> act network.ioa"
        unfolding actions_of_par by fastforce
      then show ?thesis
        using ABCD' False by fastforce
    qed
    ultimately show ?thesis
      by force
  next
    case False
    then have "a \<notin> act kmes.ioa \<and> a \<notin> act bridges.ioa \<and> a \<notin> act qkd_layer.ioa \<and> a \<notin> act network.ioa"
      unfolding actions_of_par by fastforce
    then show ?thesis
      using ABCD False by fastforce
  qed
  ultimately show ?thesis 
    by blast
qed

lemma System_trans_act_elim [elim]:
  assumes "s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t"
  shows "a \<in> act apps.ioa \<or> a \<in> act kmes.ioa \<or> a \<in> act bridges.ioa \<or> a \<in> act qkd_layer.ioa \<or> a \<in> act network.ioa"
  using assms
  unfolding trans_of_par actions_of_par by simp

end

end