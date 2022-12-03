#include "trace_manager.h"

/*@ predicate oldTraceInv(trace<EventParams> old_trace) = true; @*/

struct ConcurrentStructure *create_owicki<t>(int clientSize, list<Term> root_terms)
/*@ requires clientSize > 0 &*& PublicInv(root_terms, root(root_terms)) == true; @*/
/*@ ensures malloc_block_ConcurrentStructure(result) &*& result->mutex |-> ?l 
   &*& mutex(l,  combined_ctr(result, clientSize)) &*& 
   [1/2]result->snapshots |-> ?snap &*& snapshot_perm_forall(snap) 
   &*& result->size |-> clientSize &*& distinct(snap) == true
   &*& length(snap) == clientSize ; 
    @*/
{
     struct ConcurrentStructure *og = malloc(sizeof(struct ConcurrentStructure));
     if(og == 0){abort();}
      //@ og->snapshots = nil;
      //@ og->ghost_trace = create_ghost_cell<Trace>(root(root_terms));
      og->size = clientSize;
      //@  assert og->ghost_trace |-> ?x &*& ghost_cell(x, ?t) ;
      //@  close  valid_trace(t);

      //@ assert og->snapshots |-> ?mn;
      int i = 0; 
      //@ close   snapshot_suffix_forall(mn, t);
      //@ close  snapshot_perm_forall(mn);
        
      for(; i< clientSize; i++)
      /*@ invariant og->snapshots |-> ?p &*& snapshot_perm_forall(p) &*& length(p) == i &*& i <= clientSize &*& 
       snapshot_suffix_forall(p,  t); @*/

      {     
           
           
           //@ int  idx = create_ghost_cell(root(root_terms));
           //@ og->snapshots = (cons(idx,  p));
            
          //@ assert og->snapshots |-> ?new_snap;
          //@ assert length(new_snap) == (i+1);
          //@ assert ghost_cell(idx , ?snap_trace);
          //@ assert  snapshot_perm_forall(p);
          //@ assert og->snapshots |-> new_snap;
          //@ close valid_trace(snap_trace);
          //@ leak valid_trace(snap_trace);
          //@ close snapshot_perm_forall(new_snap);

          //@ assert  individual_snapshot_suffix(snap_trace, t) == true;
          //@ close valid_trace(snap_trace);
          //@ close snapshot_suffix_forall(new_snap, t);
          //@ leak valid_trace(snap_trace);
          //@ assert (length(new_snap) == (i+1));
         
      }

     //@ assert(i) <= clientSize;
     //@ assert(length(og->snapshots)) == clientSize;
     // we assume that each ghost cell id is unique
     //@ assume(distinct(og->snapshots) == true);
     
     //@ close combined_ctr( og, clientSize)();
     //@ close create_mutex_ghost_arg(combined_ctr(og,clientSize));

     og->mutex = create_mutex();

  return og;
}

 void acquire(struct ConcurrentStructure *og)
   /*@ requires  [?f]og->mutex |-> ?l  &*&  [f]og->size |-> ?N &*& [f]mutex(l, combined_ctr(og, N));   @*/
   /*@ ensures [f]og->mutex |-> l  &*&  [f]og->size |-> N &*& mutex_held(l, combined_ctr(og, N), currentThread, f)
   &*& combined_ctr_locked(og, N)();  @*/
{

    mutex_acquire(og->mutex);
    //@ open combined_ctr(og, N)();
    //@ assert og->ghost_trace |-> ?id;
    //@ assert ghost_cell(id, ?old_snap);
    //@ close oldTraceInv(old_snap); 
    //@ close combined_ctr_locked(og, N)();
    //@ assert true;

}

void release(struct ConcurrentStructure *og)
/*@ requires [?f]og->mutex |-> ?l   &*& [f]og->size |-> ?N &*& mutex_held(l, combined_ctr(og, N), currentThread, f)
 &*& combined_ctr_release(og, N)(); @*/
//@ ensures [f]og->mutex |-> l &*& [f]og->size |-> N &*& [f]mutex(l, combined_ctr(og, N)); 
{
  //@ open combined_ctr_release(og, N)();
  //@close  combined_ctr(og, N)();
   mutex_release(og->mutex);
   //@open oldTraceInv(?old_snap);

   
}

 struct TraceManager *create_trace_managers(int noOfClients, list<Term> root_terms)
//@ requires 2 <= noOfClients &*& PublicInv(root_terms, root(root_terms)) == true;  

/*@ ensures malloc_block_ConcurrentStructure(?og) &*& og->mutex |-> ?l &*& 
    mutex(l, combined_ctr(og, noOfClients))
    &*& ConcurrentStructure_size(og, noOfClients) &*& 
    [1/2]og->snapshots |-> ?snap 
    &*& malloc_block_chars((void *)result, (noOfClients * sizeof(struct TraceManager)))
    &*& snapshot_perm_forall(snap); @*/
{     
          //@ mul_mono_l(0, noOfClients, sizeof(struct TraceManager));      
          struct TraceManager *managers = malloc(noOfClients * sizeof(struct TraceManager));
           if(managers == 0){abort();}
           struct ConcurrentStructure *og = create_owicki(noOfClients, root_terms);
           int i = 0;
         //@ mul_mono_l(0, noOfClients, sizeof(struct TraceManager));
         //@ mul_mono_l(1, noOfClients, sizeof(struct TraceManager));
         //@ assert snapshot_perm_forall(?sn_f);
         //@ less_than_eq(noOfClients, sizeof(struct TraceManager), 1);
         //@ mul_mono_l(1, noOfClients, sizeof(struct TraceManager));
         
        
  
       //@ chars_split((void *)(managers ), sizeof(struct TraceManager));
         
           
   for(i = 0; i < noOfClients; i++)
   /*@ 
       invariant chars((void *)(managers + (i)), noOfClients*sizeof(struct TraceManager) - i*sizeof(struct TraceManager) , _) &*& i >= 0;
    @*/
   {       
         //@ less_than_eq(noOfClients, sizeof(struct TraceManager), i);
         //@ mul_mono_l(1, noOfClients, sizeof(struct TraceManager));

         //@ close_struct(managers + i);
         (managers + i)->noOfClients = noOfClients;
         (managers + i)->og = og;


         //@ open_struct(managers + i);
         //@ less_than_eq(noOfClients, sizeof(struct TraceManager), i);
         //@ mul_mono_l(1, noOfClients, sizeof(struct TraceManager));
         //@ leak(chars(_,_,_));

                              
  }


         //@ leak(chars(_,_,_));
  return managers;
  
}