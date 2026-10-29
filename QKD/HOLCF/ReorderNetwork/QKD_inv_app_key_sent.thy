theory QKD_inv_app_key_sent
  imports QKD_inv_def QKD_System_Def QKD_System_Helpers
          QKD_inv_app_kme_field_valid
begin

context QKD_Network
begin

lemma inv_app_key_sent:
  shows "invariant System.ioa (app_key_sent nodes appID)"
proof (induction rule: invariantI)
  case (1 s)
  then show ?case
  proof (cases rule: starts_of_System)
    case (1 tn qkd net)
    then show ?thesis
      unfolding app_key_sent_def by force
  qed
next
  case (2 s t a)
  then show ?case
    apply(induction rule: System_step_induct)
    using 2(2) unfolding app_key_sent_def by auto[29]
qed

end

end