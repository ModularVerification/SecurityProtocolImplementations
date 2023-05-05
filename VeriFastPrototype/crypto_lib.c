#ifndef TRACE_C
#define TRACE_C
#include "stdlib.h"
#include "threading.h"
#include "string.h"
#include "ghost_trace.h"
#include "terms.h"
#include "trace_manager.h"
#include "trace_helpers.h"
#include "crypto.h"
#include "encryption.h"
#include "gamma.h"
#include "crypto_lib.h"
//@#include "ghost_cells.gh"
//@#include <listex.gh>



pair<bool, char *> add_nonce<t>(int clientId, int noOfClients, struct TraceManager *tm, Label label, list<ParameterizedEvent> eventTypes)
/*@ requires [1/2]ghost_cell<Trace>(?snapId, ?t) &*& TraceManagerMem(tm, noOfClients, snapId) &*&  distinct(eventTypes) == true;  @*/

/*@ ensures   [1/2]ghost_cell<Trace>(snapId, ?new_snap) 
    &*& TraceManagerMem(tm, noOfClients, snapId) 
    &*& 
    fst(result) == true ? eventUniquePointer(eventTypes) &*& chars(snd(result), NonceLength, ?bytes_list)
    &*& individual_snapshot_suffix(t, new_snap) == true 
    &*& malloc_block(snd(result),NonceLength) &*& bytes_list == gamma(Nonce(bytes_list, label))
    &*& new_snap == makeNonce(_, Nonce(bytes_list, label), label) : emp;
@*/   
{     
      //@ open TraceManagerMem(tm, noOfClients, snapId);
       pair<bool, char *> nonce  = createNonce(label, eventTypes);
      if(fst(nonce))
      {     
      
      acquire(tm->og);
      //@ assert tm->og  |-> ?og;
      //@ open combined_ctr_locked(og, og->size)();
      //@ assert [_]ConcurrentStructure_snapshots(og, ?snap);

       //@ assert(chars(snd(nonce), _, ?bytes));
       //@ Term term = Nonce(bytes, label); 
       //@ write_nonce_helper(snap,  snapId, term, label, tm);     
       
       //@ close combined_ctr_release(og, og->size)(); 
      
      release(tm->og);

     
      } 

      //@ close  TraceManagerMem(tm, noOfClients, snapId);
      return nonce;

}

pair<bool, char *> Enc(int clientId, int noOfClients, struct TraceManager *tm,
                       char *msg, char *recv_pk, char *sender_sk, Term recv_pkT, int to, int from)
/*@ requires [1/2]ghost_cell<Trace>(?snapId, ?snapshot) 
   &*& TraceManagerMem(tm, noOfClients, snapId) 
   &*& [1/8]chars(msg, ?msgSize, ?msg_bytes)
   &*& [1/8]chars(recv_pk, NonceLength, ?recv_bytes) 
   &*& [1/8]chars(sender_sk, NonceLength, ?sender_bytes) 
   &*& exists<Term>(?msgT)
   &*& recv_bytes == gamma(recv_pkT) 
   &*& msg_bytes == gamma(msgT) 
   &*& (canEncrypt(snapshot, msgT, to, from, recv_pkT) || isPublishable(snapshot, msgT, pkePred) && isPublishable(snapshot, recv_pkT, pkePred));  @*/
     
     
/*@ ensures [1/2]ghost_cell<Trace>(snapId, snapshot) 
    &*& TraceManagerMem(tm, noOfClients, snapId)
    &*&  [1/8]chars(msg, msgSize, msg_bytes)
    &*& [1/8]chars(recv_pk, _, recv_bytes) 
    &*& [1/8]chars(sender_sk, _, sender_bytes)
    &*&  fst(result) == true ? chars(snd(result),  msgSize + NonceLength + 16, ?abs_ciphertext) 
    &*&  abs_ciphertext == encryptB(recv_bytes, msg_bytes)
    &*&  isPublishable(snapshot, encrypt(recv_pkT, msgT), pkePred) == true
    &*&  abs_ciphertext == (gamma(encrypt(recv_pkT, msgT))) : emp;
  
  @*/  
{     
        
      pair<bool, char *> error =  Enc_internal(msg, recv_pk, sender_sk);
      if(fst(error) != true){
      	return error;
      }
      //@ ciphertextIsPublishable(snapshot,msgT, to, from, recv_pkT );
      //@ gammaHomomorphismForEncrypt(recv_pkT, msgT);
      return error;
}


pair<bool, char *> Dec(int clientId, int noOfClients, struct TraceManager *tm,
                       char *ciphertext, char *sender_pk, char * recv_sk,  Term recv_skT, int owner)

/*@ requires  [1/2]ghost_cell<Trace>(?snapId, ?snapshot)  
    &*& TraceManagerMem(tm, noOfClients, snapId) 
    &*& [1/8]chars(ciphertext, ?msgSize, ?cipher_bytes) 
    &*& [1/8]chars(recv_sk, NonceLength, ?recv_bytes) 
    &*& [1/8]chars(sender_pk, NonceLength, ?sender_bytes) 
    &*& exists<Term>(?ciphertextT)
    &*& recv_bytes == gamma(recv_skT) &*& cipher_bytes == gamma(ciphertextT) 
    &*& (canDecrypt(snapshot, ciphertextT, recv_skT, owner)) == true; @*/
     
     
/*@ ensures [1/2]ghost_cell<Trace>(snapId, snapshot) 
    &*& TraceManagerMem(tm, noOfClients, snapId) 
    &*& exists<Term>(ciphertextT)
    &*& [1/8]chars(ciphertext, msgSize, cipher_bytes) 
    &*& [1/8]chars(recv_sk, NonceLength, recv_bytes) 
    &*& [1/8]chars(sender_pk, NonceLength, sender_bytes) 
    &*&  fst(result) == true ? chars(snd(result),  msgSize - NonceLength - 16, ?abs_msg) 
   &*&  exists<Term>(?msgT) &*& (ciphertextT == encrypt(createPk(recv_skT),msgT) ? wasDecrypted(snapshot, msgT, recv_skT, owner) == true :emp): emp;


@*/     
{     

      pair<bool, char *> error =  Dec_internal(ciphertext, recv_sk, recv_skT);
      if(fst(error) != true){
      	return error;
      }
      //@ assert chars(snd(error), ?size, ?abs_msg);
      //@ Term msgT;
      //@ close exists<Term>(msgT);
      /*@
          if(ciphertextT == encrypt(createPk(recv_skT),msgT)){
           assert exists<Term>(msgT);
           DecryptSatisfiesInvariant(snapshot, msgT, recv_skT, owner);
          }
      @*/
      return error;
}

pair<char *, char *> generateKey(int clientId, int noOfClients, struct TraceManager *tm)
/*@
 requires [1/2]ghost_cell<Trace>(?x, ?t) &*& TraceManagerMem(tm, noOfClients, x) &*& clientId == x;  @*/
 /*@
 ensures      ghost_cell<Term>(?v, ?r) &*&   chars(fst(result), NonceLength, ?abs_pk) &*& chars(snd(result), NonceLength, ?abs_sk) 
               &*& abs_pk == createPkB(abs_sk)  
               &*& abs_sk == gamma(Nonce(abs_sk, Readers(cons(x, nil))))
               &*& [1/2]ghost_cell<Trace>(x, ?val)  &*& TraceManagerMem(tm, noOfClients, x) 
               &*& individual_snapshot_suffix(t, val) == true 
               &*& r == Nonce(abs_sk, Readers(cons(x, nil)))
               &*& val == makeNonce(_, r, Readers(cons(x, nil)));

@*/    
   
{
   //@ int y = create_ghost_cell<Label>(Readers(cons(x, nil))); 
   
     pair<char *, char *>  keys = (generateKey_helper(nil));
     //@ assert chars(fst(keys), NonceLength, ?abs_pk) ;
     //@ assert chars(snd(keys), NonceLength, ?abs_sk);
     //@ open TraceManagerMem(tm, noOfClients, x);
          acquire(tm->og);
      //@ assert tm->og  |-> ?og;
      //@ open combined_ctr_locked(og, og->size)();
      //@ assert [_]ConcurrentStructure_snapshots(og, ?snap);
        //@ Label label = Readers(cons(x, nil));
      
       //@ Term term = Nonce(abs_sk, label); 
       //@ write_nonce_helper(snap,  x, term, label, tm);     
       
      //@ close combined_ctr_release(og, og->size)(); 
      
          release(tm->og);
      //@ close  TraceManagerMem(tm, noOfClients, x);
         //@ int v = create_ghost_cell<Term>(term); 
     //@ leak [1/2]ghost_cell<Label>(_,_);
     //@ leak eventUniquePointer(nil);
     return keys;
    
}
#endif