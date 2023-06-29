module RecvSentMsg
open CryptoEffect

// The participant’s identifier `a` and the message to be sent `msg` are parameters 
let send_and_receive_msg a msg =

  // Get global trace and store it in `t0`:
  let t0 = get() in

  // Send `msg` from `a` to `a` and store the trace index at which `msg` was sent in
  // variable `msg_idx`.
  // `#example` is an implicit parameter specifying the trace invariant, which is 
  // simply the least restrictive global trace invariant:
  let msg_idx = send #example a a msg in

  // At this point, there could be interference from the attacker, but DY* misses it.

  // We receive a message and store it in `received_msg`.
  // DY* requires us to provide the trace index of the corresponding send event:
  let (|_,_,received_msg|) = receive_i #example msg_idx a in

  // Get global trace and store it in `t1`:
  let t1 = get() in


  // The following assert statement *verifies incorrectly* because other participants or
  // the attacker could have added additional events to the global trace:
  assert (trace_len t1 == (trace_len t0) + 1);

  // The following assert statement *verifies incorrectly* because we prove that 
  // on all possible traces, the received message is identical to the sent message,
  // even though it could have been modified by a Dolev–Yao attacker:
  assert (received_msg == msg)
