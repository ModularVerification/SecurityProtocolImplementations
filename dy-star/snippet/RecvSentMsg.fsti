module RecvSentMsg

open SecrecyLabels
open GlobalRuntimeLib
open LabeledRuntimeAPI
open LabeledPKI
open RecvSentMsgDefinitions

(*
Demonstrates that violating granularity assumptions of a function can exclude the
attacker from operating at all.
This example here shows a participant that sends a message to itself and receives it
in the same function. We can show that the same message is received, i.e. the attacker
was provably incapable of manipulating the message, one of the base assumptions for any
Dolve-Yao style attacker.
*)

val send_and_receive_msg:
    #i: nat ->
    a: principal ->
    c_msg:msg i public ->
    LCrypto unit (pki example)
    (requires fun t0 -> i <= trace_len t0)
    (ensures fun t0 _ t1 ->
      trace_len t1 == (trace_len t0) + 1 /\
      was_message_sent_at (trace_len t0) a a c_msg)
