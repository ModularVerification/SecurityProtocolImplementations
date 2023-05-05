#ifndef CRYPTO_INTERNAL_CLIENT
#define CRYPTO_INTERNAL_CLIENT
#define NonceLength 32

#include "ghost_trace.h"
#include "terms.h"
#include "encryption.h"
#include "stdlib.h"
#include "gamma.h"
#define ParameterizedEvent EventADT<EventParams>

/* Provides cryptographic functions whose specification follows our perfect cryptography assumptions  */

/* returns a recursive predicate with a unique resources for every unique event. We add it
 as a recursive predicate since quantified permissions are not supported. */
/*@ predicate eventUniquePointer(list<ParameterizedEvent> event_types) = 
       switch(event_types)
       {
       case nil : return true;
       case cons(x, xs): return  EventUniqueResource(eventUniquenessWitness(x), getEventType(x)) &*& eventUniquePointer(xs); 
       };
@*/
/*--- Helper functions for functions in the crypto_lib ---*/

pair<bool, char *> createNonce(Label l, list<ParameterizedEvent> eventTypes);
//@ requires distinct(eventTypes) == true;
/*@ ensures fst(result)== true ? chars(snd(result), NonceLength, ?bytes_list) &*& malloc_block(snd(result), NonceLength) &*& 
   eventUniquePointer(eventTypes) &*& nonceUniqueResource(Nonce(bytes_list, l))
   &*&bytes_list == gamma(Nonce(bytes_list, l)) : emp; 
@*/


pair<bool, char *> Enc_internal( char *msg, char *recv_pk, char *sender_sk);
//@requires  [1/8]chars(msg, ?msgSize, ?msg_bytes) &*& [1/8]chars(recv_pk, NonceLength, ?recv_bytes) &*& [1/8]chars(sender_sk, NonceLength, ?sender_bytes);
/*@ensures [1/8]chars(msg, msgSize, msg_bytes) &*& [1/8]chars(recv_pk, NonceLength, recv_bytes) &*& [1/8]chars(sender_sk, NonceLength, sender_bytes) &*& 

  (fst(result) == true ? chars(snd(result),  msgSize + NonceLength + 16, ?abs_ciphertext) &*& 
  abs_ciphertext == encryptB(recv_bytes ,msg_bytes)  : emp); @*/
  
  
pair<bool, char *> Dec_internal(char *msg, char *recv_sk, Term sk);
//@requires  [1/8]chars(msg, ?msgSize, ?msg_bytes) &*& [1/8]chars(recv_sk, NonceLength, ?recv_bytes) &*&  exists<Term>(?ciphertextT);
/*@ensures [1/8]chars(msg, msgSize, msg_bytes) &*& [1/8]chars(recv_sk, NonceLength, recv_bytes) &*&
  (fst(result) == true ? chars(snd(result),  msgSize - NonceLength - 16, ?abs_ciphertext)    
   &*& exists<Term>(ciphertextT) &*& 
msg_bytes == encryptB(abs_ciphertext, recv_bytes):emp);@*/

pair<char *, char *> generateKey_helper(list<ParameterizedEvent> eventTypes);
//@ requires [1/2]ghost_cell<Label>(?x, ?l) &*& distinct(eventTypes) == true;
/*@ ensures chars(fst(result), NonceLength, ?abs_pk) &*& chars(snd(result), NonceLength, ?abs_sk) &*& abs_pk == createPkB(abs_sk) 
   &*& (abs_sk) == gamma(Nonce(abs_sk, l)) &*& eventUniquePointer(eventTypes) &*& nonceUniqueResource(Nonce(abs_sk, l)) 
   ;
@*/

#endif 
