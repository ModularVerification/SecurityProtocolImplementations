#ifndef IO_C
#define IO_C
#include "stdlib.h"
#include "threading.h"
#include "ghost_trace.h"
#include "inv_finder.h"
#include "terms.h"
#include "trace_manager.h"
#include "trace_helpers.h"
#include "crypto.h"
#include "encryption.h"
#include "gamma.h"
#include "crypto_lib.h"
//@#include "ghost_cells.gh"
//@#include <listex.gh>
//@#include "strong_ghost_lists.gh"


/* Send_helper and Receive_helper model the I/O library. 
   They enforce and yield that only messages that have 
   been recorded as sent messages on the trace can be sent 
   and received, respectively.
*/
bool Send_helper<t>(int idSender,int idReceiver, char *msg);
//@ requires  [1/2]ghost_cell<Trace>(?x, ?val) &*& exists<Term>(?msgT) &*& chars(msg, _, ?msgBytes) &*& gamma(msgT) == (msgBytes) &*& val == makeMessage(_,  idReceiver, idSender, msgT);
//@ ensures   [1/2]ghost_cell<Trace>(x, val) &*& result == true ? chars(msg, _, msgBytes) &*& exists<Term>(msgT) : exists<Term>(msgT);


 pair<bool, char *> Receive_helper<t>(int idSender,int idReceiver);
//@ requires  [1/2]ghost_cell<Trace>(?x, ?val);
//@ ensures   [1/2]ghost_cell<Trace>(x, val) &*& chars(snd(result), _, ?msgBytes)  &*& fst(result) == true ? exists<Term>(?cipher) &*& gamma(cipher) == msgBytes &*& msgOccurs(cipher, idReceiver, idSender, val) == true: emp;

bool Send<t>(int noOfClients, struct TraceManager *tm, int to, int from,  char *msg)
/*@ requires [1/2]ghost_cell<Trace>(?x, ?t) 
    &*& tm->og |-> ?og 
    &*& [?f]malloc_block_ConcurrentStructure(og) 
    &*& [f]og->mutex |-> ?l
    &*& [f]mutex(l, combined_ctr(og, noOfClients))  &*& exists<Term>(?msgT)
    &*& [f]og->size |-> noOfClients &*& [f/2]og->snapshots |-> ?snap &*& mem(x, snap) == true 
    &*& distinct(snap) == true  &*& messageInv(to,from, msgT, t, pkePred) == true 
    &*& chars(msg, _, ?msgBytes) &*& gamma(msgT) == (msgBytes);  @*/
 
/*@ ensures TraceManagerMem(tm, noOfClients, x) &*& mem(x, snap) == true 
 &*& 
     [1/2]ghost_cell<Trace>(x, ?val) &*&  individual_snapshot_suffix(t, val) == true &*& exists<Term>(msgT) &*&
    distinct(snap) == true &*&  result == true ? val == makeMessage(_,  to, from, msgT) &*& chars(msg, _, msgBytes ) : emp;
  @*/   
{     

      acquire(tm->og);
      

      //@ open combined_ctr_locked(og, og->size)();
      //@ write_message_helper(snap,  x, to, from, msgT,  tm);
      //@ close combined_ctr_release(og, og->size)();
      release(tm->og);
      bool err = Send_helper(from, to, msg);
      //@close TraceManagerMem(tm, noOfClients, x);
     return err;
}


pair<bool, char *> Receive<t>(int noOfClients, struct TraceManager *tm, int to, int from)
/*@ requires [1/2]ghost_cell<Trace>(?x, ?t) 
  &*&  tm->og |-> ?og
  &*& [?f]malloc_block_ConcurrentStructure(og)
  &*& [f]og->mutex |-> ?l
  &*& [f]mutex(l, combined_ctr(og, noOfClients)) 
  &*& [f]og->size |-> noOfClients
  &*& [f/2]og->snapshots |-> ?snap &*& mem(x, snap) == true 
  &*& distinct(snap) == true ;@*/
 
/*@ ensures TraceManagerMem(tm, noOfClients, x) &*& mem(x, snap) == true 
    &*& [1/2]ghost_cell<Trace>(x, ?val)
    &*&  individual_snapshot_suffix(t, val) == true  
    &*&  chars(snd(result), _, ?msgBytes)  
    &*& distinct(snap) == true 
    &*&  fst(result) == true ? 
     exists<Term>(?msgT)&*& gamma(msgT) == msgBytes &*& 
      msgOccurs(msgT, to, from, val) == true  &*& messageInv(to, from, msgT, val, pkePred) == true : emp; 

  @*/   
{     
      

     
       

      acquire(tm->og);
      //@ open combined_ctr_locked(og, og->size)();


      //@ assert [1/2]ghost_cell<Trace>(x, _);
      //@ sync(snap,  x,  tm);
     //@ close combined_ctr_release(og, og->size)();
     //@ assert  [1/2]ghost_cell<Trace>(x, ?val); 
      release(tm->og);
      
       pair<bool, char *> temp_pair= Receive_helper( from, to);
       
       acquire(tm->og);
      //@ open combined_ctr_locked(og, og->size)();
      /*@ if(fst(temp_pair)){
            snapshot_reflexive(val);
            assert exists<Term>(?cipher);
            assert ghost_cell<Trace>(_, ?new_val); 
            
            trace<EventParams> prev = getMsgInvWrapper(new_val, snap, val, x,cipher, to, from);
            isPublishableMonotonic(prev, val,  cipher, pkePred);
        }
      @*/
      //@ close combined_ctr_release(og, og->size)();
      release(tm->og);

       //@close TraceManagerMem(tm, noOfClients, x);
     return temp_pair;
}

