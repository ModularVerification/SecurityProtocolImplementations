#ifndef TRACE_HELPER
#define TRACE_HELPER
#include "ghost_trace.h"
#include "terms.h"
#include "trace_manager.h"
#include "crypto.h"
/*@ 

  /* Wraps the memory related predicates for TraceManagers */
  predicate TraceManagerMem(struct TraceManager *tm, int noOfClients, int x) = 
  tm->og |-> ?og &*& [?f]malloc_block_ConcurrentStructure(og) &*& [f]og->mutex |-> ?l &*& [f]mutex(l, combined_ctr(og, noOfClients)) 
  &*& [f]og->size |-> noOfClients &*& [f/2]og->snapshots |-> ?snap &*& mem(x, snap) == true 
  &*& distinct(snap) == true; 
  
  
@*/ 

/* Adds an event to the trace */
void *add_event(int clientId, int noOfClients, struct TraceManager *tm, int principal);
/*@ requires [1/2]ghost_cell<Trace>(?x, ?t) &*& TraceManagerMem(tm, noOfClients, x)   
    &*& exists<ParameterizedEvent >(?e)   &*&  event_pred(principal, e, t) ;  @*/  
    
/*@ ensures TraceManagerMem(tm, noOfClients, x)  &*& [1/2]ghost_cell<Trace>(x, ?val)  &*&  individual_snapshot_suffix(t, val) ==true  
   &*& val == makeEvent(_,  principal, e); @*/   




/*@

/* Helper function for write nonce that unfolds the snapshot_permission_forall predicate 
   and updates the trace, ensuring that valid trace predicate is maintained.  
*/
lemma void write_nonce_helper(list<int> snap, int x, Term term, Label label, struct TraceManager *tm);
  requires  tm->og |-> ?og &*&  term == Nonce(_,_) &*& 
  [?f]malloc_block_ConcurrentStructure(og) &*& [1/2]ghost_cell<Trace>(x, ?t)  &*& 
  mem(x, snap) == true &*& distinct(snap) == true &*& nonceUniqueResource(term) 
  &*& og->ghost_trace |-> ?id  &*& ghost_cell<Trace>(id, ?global_trace) &*& valid_trace(global_trace)
  &*&   snapshot_suffix_forall(snap,global_trace);

 ensures  ghost_cell(id, ?new_global_trace) &*&
     snapshot_suffix_forall(snap, new_global_trace) &*& mem(x, snap) == true &*&
    [1/2]ghost_cell<Trace>(x, ?val) &*& distinct(snap) == true  &*& valid_trace(new_global_trace)
    &*& ConcurrentStructure_ghost_trace(og, id) &*&   mem(x,snap) ==true &*& val == new_global_trace
    &*& individual_snapshot_suffix(t, val) == true &*& 
  [f]malloc_block_ConcurrentStructure(og) &*& TraceManager_og(tm, og) &*& new_global_trace ==  makeNonce(global_trace, term, label);

/* Helper function for add_message that unfolds the snapshot_permission_forall predicate 
   and updates the trace, ensuring that valid trace predicate is maintained.  
*/
lemma void write_message_helper<t>(list<int> snap, int x, int to, int from, Term term,  struct TraceManager *tm);
  requires  tm->og |-> ?og &*&  
  [?f]malloc_block_ConcurrentStructure(og) &*& [1/2]ghost_cell<Trace>(x, ?t)  &*& 
  mem(x, snap) == true &*& distinct(snap) == true 
  &*& og->ghost_trace |-> ?id  &*& ghost_cell<Trace>(id, ?global_trace) &*& valid_trace(global_trace)
  &*&   snapshot_suffix_forall(snap, global_trace) &*& isPublishable(t, term, pkePred) == true;

 ensures  ghost_cell(id, ?new_global_trace) &*&
     snapshot_suffix_forall(snap,new_global_trace) &*& mem(x, snap) == true &*&
    [1/2]ghost_cell<Trace>(x, ?val) &*& distinct(snap) == true  &*& valid_trace(new_global_trace)
    &*& ConcurrentStructure_ghost_trace(og, id) &*&   mem(x,snap) ==true &*& val == new_global_trace 
     &*& individual_snapshot_suffix(t, val) == true &*&
  [f]malloc_block_ConcurrentStructure(og) &*& TraceManager_og(tm, og) &*& new_global_trace == makeMessage(global_trace,  to, from, term);
	

/* Helper function for write event that unfolds the snapshot_permission_forall predicate 
   and updates the trace, ensuring that valid trace predicate is maintained.  
*/
      
lemma void write_event_helper(list<int> snap, int x, int principal, EventADT<EventParams> e, struct TraceManager *tm);
  requires  tm->og |-> ?og &*&  
  [?f]malloc_block_ConcurrentStructure(og) &*& [1/2]ghost_cell<Trace>(x, ?t)  &*& 
  mem(x, snap) == true &*& distinct(snap) == true
  &*& og->ghost_trace |-> ?id  &*& ghost_cell<Trace>(id, ?global_trace) &*& valid_trace(global_trace)
  &*&   snapshot_suffix_forall(snap, global_trace) &*& 
  event_pred(principal, e, t) ;
 

 ensures  ghost_cell(id, ?new_global_trace) &*&
     snapshot_suffix_forall(snap, new_global_trace) &*& mem(x, snap) == true &*&
    [1/2]ghost_cell<Trace>(x, ?val) &*& distinct(snap) == true  &*& valid_trace(new_global_trace)
    &*& ConcurrentStructure_ghost_trace(og, id) &*&   mem(x,snap) ==true &*& val == new_global_trace &*& 
  [f]malloc_block_ConcurrentStructure(og) &*& TraceManager_og(tm, og) &*& new_global_trace == makeEvent(global_trace,  principal, e)
   &*& trace_length(new_global_trace) <= 1 + trace_length(global_trace);
  
/* 
 Helper function that updates snapshot to the current global trace. 
*/
lemma void sync(list<int> snap, int x, struct TraceManager *tm);
requires  tm->og |-> ?og &*&   [1/2]ghost_cell<Trace>(x, ?t)  &*& 
  [?f]malloc_block_ConcurrentStructure(og)   &*& 
  mem(x, snap) == true &*& distinct(snap) == true
  &*& og->ghost_trace |-> ?id  &*& ghost_cell<Trace>(id, ?global_trace) &*& valid_trace(global_trace)
  &*&   snapshot_suffix_forall(snap, global_trace);
  
 ensures  ghost_cell(id, global_trace) &*&
     snapshot_suffix_forall(snap, global_trace) &*& mem(x, snap) == true &*&
    [1/2]ghost_cell<Trace>(x, global_trace) &*& distinct(snap) == true  &*& valid_trace(global_trace)
    &*& ConcurrentStructure_ghost_trace(og, id) &*&   mem(x,snap) ==true &*& 
   [f] malloc_block_ConcurrentStructure(og) &*& TraceManager_og(tm, og) &*& individual_snapshot_suffix(t, global_trace) == true;

   @*/
#endif