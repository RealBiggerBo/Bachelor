theory QKD_Channel_Definitions_IOA          
  imports QKD_Channel_IOA
begin

section Fifo_Channels

abbreviation add_msg where
  \<open>add_msg s sender rcpt m \<equiv> s((sender, rcpt) := s((sender, rcpt)) @ [m])\<close>

abbreviation rmv_msg where
  \<open>rmv_msg s sender rcpt m \<equiv> s((sender, rcpt) := tl (s((sender, rcpt))))\<close>

abbreviation can_send where
  \<open>can_send s sender rcpt m \<equiv> if s((sender, rcpt)) = [] then False else m = hd (s((sender, rcpt)))\<close>

locale FifoChannel
begin

sublocale Channel
  "\<lambda>set. []"
  "\<lambda>s sender rcpt m. add_msg s sender rcpt m"
  "\<lambda>s sender rcpt m. rmv_msg s sender rcpt m"
  "\<lambda>s sender rcpt m. can_send s sender rcpt m"
  .



end

end