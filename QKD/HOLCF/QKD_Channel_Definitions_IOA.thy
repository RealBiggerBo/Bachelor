theory QKD_Channel_Definitions_IOA          
  imports QKD_Channel_IOA
begin

section Set_Channels

locale Lossy_Reorder_SetChannel = 
  fixes pids :: "'proc set"
begin

sublocale Set_Channel
  pids
  "{}"
  "\<lambda>s sender rcpt m. s \<union> {(sender, rcpt, m)}"
  "\<lambda>s _ _ _. s"
  "\<lambda>s sender rcpt m. (sender, rcpt, m) \<in> s"
  .

end

end