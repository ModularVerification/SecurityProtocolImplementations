#include "trace_helpers.h"
#include "crypto.h"

void *add_event(int clientId, int noOfClients, struct TraceManager *tm, int principal)
/*@ requires [1/2]ghost_cell<Trace>(?x, ?t) &*& TraceManagerMem(tm, noOfClients, x) 
    &*& exists<ParameterizedEvent >(?e)  &*&  event_pred(principal, e, t) ;  @*/  
    
/*@ ensures TraceManagerMem(tm, noOfClients, x)  &*& [1/2]ghost_cell<Trace>(x, ?val) &*&  individual_snapshot_suffix(t, val) ==true  
    &*& val == makeEvent(_,  principal, e); @*/   
{     
      //@ open TraceManagerMem(tm, noOfClients, x);
         acquire(tm->og);

      //@ assert tm->og  |-> ?og;
      //@ open combined_ctr_locked(og, og->size)();
      //@ assert [?f]ConcurrentStructure_snapshots(og, ?snap);
      //@ assert valid_trace(?global_trace);
      //@ assert oldTraceInv(global_trace);
      //  merge_fractions ConcurrentStructure_snapshots(og, snap);

      //@ write_event_helper(snap,  x, principal, e,  tm); 
      //@ close combined_ctr_release(og, og->size)();
       release(tm->og);
      //@close TraceManagerMem(tm, noOfClients, x);
      return tm;
}




/*@

lemma void write_nonce_helper(list<int> snap, int x, Term term, Label label, struct TraceManager *tm)
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
 [f] malloc_block_ConcurrentStructure(og) &*& TraceManager_og(tm, og) &*& new_global_trace ==  makeNonce(global_trace, term, label);
  { 
 
  switch(snap){
    case nil:     
         open snapshot_suffix_forall(snap, global_trace);
         close snapshot_suffix_forall(snap,  global_trace);

    case cons(l, ls): 
         open snapshot_suffix_forall(snap,  global_trace);
  		if(x == l){
 			 merge_fractions ghost_cell(x,_); 
  		         trace<EventParams> val = makeNonce(global_trace, term, label);
  		         ghost_cell_mutate<Trace>(x, val);
  		         split_fraction ghost_cell(x, val) by 1/2;
  		         ghost_cell_mutate<Trace>(id, val);
  		         assert ghost_cell(id, ?new_gt);
                         open nonceUniqueResource(term);
  		         close valid_trace(val);
  		         snapshot_suffix_hold_nonce(val, ls);
                         close snapshot_suffix_forall(snap,  new_gt);
                       }
  else 
     {
   	 write_nonce_helper(ls, x, term, label, tm);
    	 assert snapshot_suffix_forall(ls, ?new_global_trace);
    	 individual_snapshot_suffix(global_trace, new_global_trace);
         close snapshot_suffix_forall(snap,  new_global_trace);
     }
  }
}

@*/
/*@

lemma void write_message_helper<t>(list<int> snap, int x, int to, int from, Term term,  struct TraceManager *tm)
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
  { 
 
  switch(snap){
    case nil:     
         open snapshot_suffix_forall(snap, global_trace);
         close snapshot_suffix_forall(snap, global_trace);

    case cons(l, ls): 
         open snapshot_suffix_forall(snap,  global_trace);
  		if(x == l){
 			 merge_fractions ghost_cell(x,_); 
  		         Trace val = makeMessage(global_trace,  to, from, term);
  		         ghost_cell_mutate<Trace>(x, val);
  		         split_fraction ghost_cell(x, val) by 1/2;
  		         ghost_cell_mutate<Trace>(id, val);
  		         assert ghost_cell(id, ?new_gt);
  		        //  close messageInv(to, from, term, t, pkePred);
  		         snapshot_suffix_hold_adding_message(global_trace,val);          
  		         snapshot_suffix_hold_message(val, ls);
                         messageInvMonotonic(t,  global_trace, to, from, term, pkePred);
  		         close valid_trace(val);
                         close snapshot_suffix_forall(snap, new_gt);
                       }
  else 
     {
   	 write_message_helper(ls, x, to, from, term, tm);
    	 assert snapshot_suffix_forall(ls, ?new_global_trace);
    	 individual_snapshot_suffix(global_trace, new_global_trace);
         close snapshot_suffix_forall(snap, new_global_trace);
     }
  }
}
   
      
 lemma void write_event_helper(list<int> snap, int x, int principal, EventADT<EventParams> e, struct TraceManager *tm)
  requires  tm->og |-> ?og &*&  
  [?f]malloc_block_ConcurrentStructure(og) &*& [1/2]ghost_cell<Trace>(x, ?t)  &*& 
  mem(x, snap) == true &*& distinct(snap) == true
  &*& og->ghost_trace |-> ?id  &*& ghost_cell<Trace>(id, ?global_trace) &*& valid_trace(global_trace)
  &*&   snapshot_suffix_forall(snap, global_trace) &*& 
  event_pred(principal, e, t) ;
 

 ensures  ghost_cell(id, ?new_global_trace) &*&
     snapshot_suffix_forall(snap, new_global_trace) &*& mem(x, snap) == true &*&  individual_snapshot_suffix(t, new_global_trace) == true
     &*& [1/2]ghost_cell<Trace>(x, ?val) &*& distinct(snap) == true  &*& valid_trace(new_global_trace)
    &*& ConcurrentStructure_ghost_trace(og, id) &*&   mem(x,snap) ==true &*& val == new_global_trace &*& 
 [f] malloc_block_ConcurrentStructure(og) &*& TraceManager_og(tm, og) &*& new_global_trace == makeEvent(global_trace,  principal, e)
 &*& trace_length(new_global_trace) <= 1 + trace_length(global_trace);
  { 
 
  switch(snap){
    case nil:     
                 open snapshot_suffix_forall(snap, global_trace);
                  close snapshot_suffix_forall(snap,  global_trace);

    case cons(l, ls): 
      open snapshot_suffix_forall(snap, global_trace);
  		if(x == l){
 			 merge_fractions ghost_cell(x,_); 
  		        Trace val = makeEvent(global_trace,  principal, e);
  		        ghost_cell_mutate<Trace>(x, val);
  		        split_fraction ghost_cell(x, val) by 1/2;
  		        ghost_cell_mutate<Trace>(id, val);
  		        assert ghost_cell(id, ?new_gt);
  		        eventPredMonotonic(t, global_trace, principal, e);
  		        close valid_trace(val);
  		        snapshot_suffix_hold_event(val, ls);
                        close snapshot_suffix_forall(snap,  val);
                  }
  else {

    write_event_helper(ls, x, principal, e, tm);
    assert snapshot_suffix_forall(ls,  ?new_global_trace);
    individual_snapshot_suffix(global_trace, new_global_trace);
    close snapshot_suffix_forall(snap,  new_global_trace);


  }
  }
  

  }
  
  
lemma void sync(list<int> snap, int x, struct TraceManager *tm)
requires  tm->og |-> ?og &*&  
  [?f]malloc_block_ConcurrentStructure(og) &*& [1/2]ghost_cell<Trace>(x, ?t)  &*& 
  mem(x, snap) == true &*& distinct(snap) == true
  &*& og->ghost_trace |-> ?id  &*& ghost_cell<Trace>(id, ?global_trace) &*& valid_trace(global_trace)
  &*&   snapshot_suffix_forall(snap, global_trace);
  
 ensures  ghost_cell(id, global_trace) &*&
     snapshot_suffix_forall(snap, global_trace) &*& mem(x, snap) == true &*&
    [1/2]ghost_cell<Trace>(x, global_trace) &*& distinct(snap) == true  &*& valid_trace(global_trace)
    &*& ConcurrentStructure_ghost_trace(og, id) &*&   mem(x,snap) ==true &*& 
    [f]malloc_block_ConcurrentStructure(og) &*& TraceManager_og(tm, og) &*& individual_snapshot_suffix(t, global_trace) == true;
    {
    
  switch(snap){
    case nil:   
    case cons(l, ls): 
      open snapshot_suffix_forall(snap, global_trace);
  		if(x == l){
 			 merge_fractions ghost_cell(x,_); 
  		         ghost_cell_mutate<Trace>(x, global_trace);
  		         split_fraction ghost_cell(x, global_trace) by 1/2;
  		         snapshot_reflexive(global_trace);
               close snapshot_suffix_forall(snap,  global_trace);
                  }
  else {

    sync(ls, x, tm);
    close snapshot_suffix_forall(snap,  global_trace);


  }
  }
  

    
    
    
    }
  @*/