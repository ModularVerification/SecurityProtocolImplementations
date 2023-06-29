/// NSL.Protocol (implementation)
/// ==============================
module NSL.Protocol
open SecurityLemmas

val responder_receive_msg_1_helper:
  #i:nat ->
  b: principal ->
  c_msg1:msg i public ->
  skb: priv_key i b ->
  LCrypto (a:principal * n_a:msg i (readers [P b])) (pki nsl)
    (requires (fun _ -> True))
    (ensures (fun t0 (a, n_a) t1 -> trace_len t0 == trace_len t1 /\
			  (is_publishable nsl_global_usage i n_a \/
			  (was_rand_generated_before i n_a (readers [P a;P b]) (nonce_usage "NSL.nonce")))))

let responder_receive_msg_1_helper #i b c_msg1 skb =
  match pke_dec #nsl_global_usage #i #(readers [P b]) skb c_msg1 with
  | Success msg1 ->
    (let l = readers [P b] in
    let pkb = pk #nsl_global_usage #i #(readers [P b]) skb in
    readers_is_injective b;
    match parse_valid_message #i #(get_label nsl_key_usages msg1) msg1 with
    | Success (Msg1 n_a a) ->
      assert (is_msg nsl_global_usage i n_a l);
      can_flow_transitive i (get_label nsl_key_usages n_a) (get_label nsl_key_usages msg1) public;
      can_flow_transitive i (get_label nsl_key_usages n_a) (get_label nsl_key_usages msg1) l;
      (a, n_a)
    | _ -> error "wrong msg_1 tag")
  | _ -> error "decrypt failed"


val responder_send_msg_2_helper:
  #i:nat ->
  b:principal ->
  a:principal ->
  pka: pub_key i a ->
  n_a: msg i (readers [P b]){
    is_publishable nsl_global_usage i n_a \/
    was_rand_generated_before i n_a (readers [P a;P b]) (nonce_usage "NSL.nonce")
  } ->
  n_b:ns_nonce i a b{
    did_event_occur_before i b (respond a b n_a n_b)} ->
  n_pke:pke_nonce nsl_global_usage i (readers [P b]) ->
  msg i public

let responder_send_msg_2_helper #i b a pka n_a n_b n_pke =
  rand_is_secret #nsl_global_usage #i #(readers [P a; P b]) #(nonce_usage "NSL.nonce") n_a;
  let n_a:msg i (readers [P a; P b]) = n_a in
  let msg2 : msg i (readers [P a; P b]) = serialize_valid_message i (Msg2 n_a n_b b) (readers [P a; P b]) in
  let msg2' = restrict msg2 (readers [P a]) in
  let msg2'' = restrict msg2 (readers [P b]) in
  assert (get_label nsl_key_usages msg2'' == get_label nsl_key_usages msg2);
  sk_label_lemma nsl_global_usage i pka (readers [P a]);
  let c_msg3 = pke_enc #nsl_global_usage #i pka n_pke msg2' in
  c_msg3

let responder_send_msg_2 b msg_idx =
  let (|now,_,c_msg1|) = receive_i #nsl msg_idx b in
  let (|_, skb|) = get_private_key #nsl #now b PKE "NSL.key" in
  let (a, n_a) = responder_receive_msg_1_helper #now b c_msg1 skb in
  let pka = get_public_key #nsl #now b a PKE "NSL.key" in
  let (|t0, n_b|) = rand_gen #nsl (readers [P a; P b]) (nonce_usage "NSL.nonce") in
  let ev = respond a b n_a n_b in
  trigger_event #nsl b ev;
  let t1 = global_timestamp () in
  let si = new_session_number #nsl b in
  let new_ss_st = ResponderSentMsg2 a n_a n_b in
  let new_ss = serialize_valid_session_st t1 b si 0 new_ss_st in
  new_session #nsl #t1 b si 0 new_ss;
  let (|t2,n_pke|) = rand_gen #nsl (readers [P b]) (nonce_usage "PKE_NONCE") in
  let c_msg2 = responder_send_msg_2_helper #t2 b a pka n_a n_b n_pke in
  let now = send #nsl #t2 b a c_msg2 in
  (si, now)

let n_b_pred i a b n_a n_b =
	(is_publishable nsl_global_usage i n_b /\ can_flow i (readers [P a; P b]) public /\ (corrupt_id i (P a) \/ corrupt_id i (P b))) \/
	  (did_event_occur_before i b (respond a b n_a n_b) /\
	    was_rand_generated_before i n_b (readers [P a;P b]) (nonce_usage "NSL.nonce"))

let initiator_receive_msg_2_helper (i:nat) (a:principal) (b:principal) (c_msg2:msg i public)
				   (ska:priv_key i a) (n_a:ns_nonce i a b) :
    LCrypto (msg i (readers [P a])) (pki nsl) (requires (fun _ -> True)) (ensures (fun t0 (n_b) t1 -> n_b_pred i a b n_a n_b))
= match pke_dec #nsl_global_usage #i #(readers [P a]) ska c_msg2 with 
  | Success msg2 ->
    (let l = readers [P a] in
    let pka = pk #nsl_global_usage #i #(readers [P a]) ska in 
    readers_is_injective a;
    match parse_valid_message #i #(get_label nsl_key_usages msg2) msg2 with
    | Success (Msg2 n_a' n_b b') ->
      if n_a = n_a' && b = b' then (
	includes_corrupt_2_lemma i (P a) (P b);
	n_b)
      else error "n_a or b did not match"
    | _ -> error "wrong msg_2 tag")
  | _ -> error "decrypt failed"

let initiator_send_msg_3_helper (#i:nat) (a:principal) (b:principal) (pkb: pub_key i b) (n_a: ns_nonce i a b)
    (n_b: msg i (readers [P a]){did_event_occur_before i a (finishI a b n_a n_b) /\ n_b_pred i a b n_a n_b})
    (n_pke: pke_nonce nsl_global_usage i (readers [P a]))
  : msg i public
= let l = get_label nsl_key_usages n_b in
  let l_b =  (readers [P a;P b]) in
  flows_to_public_can_flow i l l_b;
  rand_is_secret #nsl_global_usage #i #(readers [P a; P b]) #(nonce_usage "NSL.nonce") n_b;
  let msg3 = serialize_valid_message i (Msg3 n_b a) l_b in
  let msg3' = restrict msg3 (readers [P b]) in
  let msg3'' = restrict msg3 (readers [P a]) in
  assert (get_label nsl_key_usages msg3'' == get_label nsl_key_usages msg3);
  sk_label_lemma nsl_global_usage i pkb (readers [P b]);
  pke_enc #nsl_global_usage #i pkb n_pke msg3'

#push-options "--z3rlimit 100"

// the following function contains the implementation of both
// `initiator_send_msg_1` and `initiator_send_msg_3`. We violate
// on purpose DY*'s assumption that protocol steps must be located
// in different functions, which is not in general the case for
// existing implementations. With this code structure, we can prove
// that the initiator receives a message without the responder sending
// it (because there is no corresponding send event on the trace
// between the two protocol steps of the initiator)! That is, either
// the initiator or the responder must have been corrupted. Since this
// reasoning applies to all possible executions of the protocol, we
// have proved that the NSL protocol cannot be executed without
// cooperation from the attacker, which is clearly not the case.
// Furthermore, this allows us to send the nonces `na` and `nb` in
// plaintext to the network.
let initiator_send_msg_1_and_msg_3 a b msg2_idx =
  let si = new_session_number #nsl a in
  let (|t0, n_a|) = rand_gen #nsl (readers [P a; P b]) (nonce_usage "NSL.nonce") in
  let ev = initiate a b n_a in 
  trigger_event #nsl a ev;
  let t1 = global_timestamp () in
  let m = Msg1 n_a a in
  let l = readers [P a; P b] in
  let msg1' : msg t1 l = serialize_valid_message t1 m l in
  let msg1'' = restrict msg1' (readers [P b]) in
  let msg1''' = restrict msg1' (readers [P a]) in
  assert (get_label nsl_key_usages msg1''' == get_label nsl_key_usages msg1');
  let pkb = get_public_key #nsl #t1 a b PKE "NSL.key" in 
  sk_label_lemma nsl_global_usage t1 pkb (readers [P b]);
  let (|t2,n_pke|) = rand_gen #nsl (readers [P a]) (nonce_usage "PKE_NONCE") in
  let c_msg1 = pke_enc #nsl_global_usage #t2 #(readers [P a]) pkb n_pke msg1'' in
  
  // send msg1
  let t1_send = send #nsl #t2 a b c_msg1 in

  // At this point, there could be interference from any participant or the attacker,
  // but DY* misses it since its assumptions on the code structure are violated in
  // this example.

  // receive msg2
  let (|t3,_,c_msg2|) = receive_i #nsl msg2_idx a in
  let (|_,ska|) = get_private_key #nsl #t3 a PKE "NSL.key" in
  let pkb = get_public_key #nsl #t3 a b PKE "NSL.key" in
  let n_b = initiator_receive_msg_2_helper t3 a b c_msg2 ska n_a in
  assert (n_b_pred t3 a b n_a n_b);

  // By msg2's invariant, we can prove that either the respond event or corruption has occurred:
  assert (corrupt_id t3 (P a) \/ corrupt_id t3 (P b) \/ (did_event_occur_before t3 b (respond a b n_a n_b)));

  // Using the event invariant of respond, we can derive that the responder must have created the
  // nonce n_b after n_a unless corruption occurred:
  assert (corrupt_id t3 (P a) \/ corrupt_id t3 (P b) \/ (
    exists resp_idx. t0 < resp_idx /\
      was_rand_generated_at (resp_idx-1) n_b (readers [P a; P b]) (nonce_usage "NSL.nonce") /\
      was_rand_generated_before (resp_idx-1) n_a (readers [P a; P b]) (nonce_usage "NSL.nonce") \/
        is_publishable nsl_global_usage resp_idx n_a));

  includes_corrupt_2_lemma_forall_trace_index (P a) (P b);

  // Since we know all trace entries since creating the nonce n_a (due to missing the interference for 
  // other participants and the attacker), n_b cannot have been created by the responder.
  // Thus, the following assert statement *verifies incorrectly* expressing that on all possible traces
  // either a or b must have been corrupted. I.e., we prove that there is no protocol run
  // in which the attacker does not corrupt any participant:
  assert (corrupt_id t3 (P a) \/ corrupt_id t3 (P b));

  let ev = finishI a b n_a n_b in
  trigger_event #nsl a ev;
  let t4 = global_timestamp () in
  let new_ss_st = InitiatorSentMsg3 b n_a n_b in
  rand_is_secret #nsl_global_usage #t4 #(readers [P a; P b]) #(nonce_usage "NSL.nonce") n_b;
  let new_ss = serialize_valid_session_st t4 a si 0 new_ss_st in 
  new_session #nsl #t4 a si 0 new_ss;

  // since we just incorrectly proved that corruption must have always occurred
  // at this program point, we can now simply send n_a and n_b in plaintext to the network:
  let n_a:msg t4 public = n_a in
  let n_b:msg t4 public = n_b in
  // we construct `plaintext_containing_na_nb`, which is a serialized but *not encrypted*
  // message containing `n_a` and `n_b` ...
  let plaintext_containing_na_nb = serialize_valid_message t4 (Msg2 n_a n_b b) public in
  // ... and send `plaintext_containing_na_nb`:
  let t5 = send #nsl #t4 a b plaintext_containing_na_nb in
  (si, t1_send, t5)

let responder_receive_msg_3_helper (#i: nat) (b: principal) (a: principal) (c_msg3: msg i public) (skb: priv_key i b) (n_b: ns_nonce i a b) :
    LCrypto unit (pki nsl) (requires (fun _ -> True)) (ensures fun t0 _ t1 -> corrupt_id i (P a) \/ corrupt_id i (P b) \/
								     (exists n_a. did_event_occur_before i a (finishI a b n_a n_b)))
= match pke_dec #nsl_global_usage #i #(readers [P b]) skb c_msg3 with 
  | Success msg3 ->
    (let l = readers [P b] in
    let pkb = pk #nsl_global_usage #i #l skb in 
    readers_is_injective b;
    match parse_valid_message #i #(get_label nsl_key_usages msg3) msg3 with
    | Success (Msg3 n_b' a') ->
      if n_b = n_b' && a = a' then includes_corrupt_2_lemma i (P a) (P b)
      else error "n_b did not match"
    | _ -> error "wrong msg_3 tag")
  | _ -> error "decrypt failed"

let responder_receive_msg_3 b idx_resp_session msg_idx =
  let t0 = global_timestamp () in
  let (|vi,st|) = get_session #nsl #t0 b idx_resp_session in
  match parse_session_st st with
  | Success (ResponderSentMsg2 a n_a n_b) ->
    let (|now,_,c_msg3|) = receive_i #nsl msg_idx b in
    let (|_,skb|) = get_private_key #nsl #now b PKE "NSL.key" in 
    responder_receive_msg_3_helper #now b a c_msg3 skb n_b;
    let ev = finishR a b n_a n_b in 
    trigger_event #nsl b ev;
    let t1 = global_timestamp () in
    let new_ss_st = ResponderReceivedMsg3 a n_b in
    let new_ss = serialize_valid_session_st t1 b idx_resp_session vi new_ss_st in
    update_session #nsl #t1 b idx_resp_session vi new_ss
  |_ -> error "parse error"
#pop-options
