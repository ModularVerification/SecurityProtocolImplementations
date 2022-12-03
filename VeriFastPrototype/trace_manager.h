#ifndef TRACE_MANAGER
#define TRACE_MANAGER
#include "stdlib.h"
#include "threading.h"
#include "string.h"
#include "ghost_trace.h"
#include "terms.h"
//@#include "ghost_cells.gh"
//@#include <listex.gh>
//@#include "strong_ghost_lists.gh"

/* 
   Struct that defines the concurrent data structure. snapshots is a list of integers 
   which co-respond to ghost cells where the snapshot is stored. ghost_trace 
   co-responds to the cell where the global trace is stored.
*/

struct ConcurrentStructure {
 //@ list<int> snapshots; 
 //@ int ghost_trace;
 int size;
 struct mutex *mutex;
};


/* Predicate constructor for the mutex that protects the global trace and the 
   [1/2] permission to other snapshots */
/*@
predicate_ctor combined_ctr(struct ConcurrentStructure *og, int size)() =  
og->ghost_trace |-> ?x &*& [1/2]og->snapshots |-> ?snap &*& ghost_cell<Trace>(x, ?t) &*& valid_trace(t) 
&*& snapshot_suffix_forall(snap, t);
   
@*/

/*@ 
// `oldTraceInv` keeps track of the track at the point of time immediately after aquiring the ghost
// lock. This enables release to check that the trace has been extended only with at most one trace
// entry to ensure atomicity.
predicate oldTraceInv(trace<EventParams> old_trace);

predicate_ctor combined_ctr_locked(struct ConcurrentStructure *og, int size)() =  
og->ghost_trace |-> ?x &*& [1/2]og->snapshots |-> ?snap &*& ghost_cell<Trace>(x, ?t) &*& valid_trace(t) 
&*& snapshot_suffix_forall(snap, t) &*& oldTraceInv(t);

predicate_ctor combined_ctr_release(struct ConcurrentStructure *og, int size)() =  
og->ghost_trace |-> ?x &*& [1/2]og->snapshots |-> ?snap &*& ghost_cell<Trace>(x, ?t) &*& valid_trace(t) 
&*& snapshot_suffix_forall(snap, t) &*& oldTraceInv(?old_trace) &*& trace_length(old_trace) <= 1 + trace_length(t);
@*/

/* Trace Manager struct that contains the ConcurrentStructure Counter */     
struct TraceManager{
  int noOfClients;
  struct ConcurrentStructure *og;

};

/* Creates an ConcurrentStructure Counter and return the permission */
struct ConcurrentStructure *create_owicki<t>(int clientSize, list<Term> root_terms);
/*@ requires clientSize > 0 &*& PublicInv(root_terms, root(root_terms)) == true; @*/
/*@ ensures malloc_block_ConcurrentStructure(result) &*& result->mutex |-> ?l &*& mutex(l,  combined_ctr(result, clientSize)) &*& 
   [1/2]result->snapshots |-> ?snap &*& snapshot_perm_forall(snap) &*& result->size |-> clientSize &*& distinct(snap) == true
   &*& length(snap) == clientSize ;  @*/

/* Wrapper for the mutex function acquire in threading.h */
void acquire(struct ConcurrentStructure *og);

  /*@ requires  [?f]og->mutex |-> ?l  &*&  [f]og->size |-> ?N &*& [f]mutex(l, combined_ctr(og, N));   @*/
   /*@ ensures mutex_held(l, combined_ctr(og, N), currentThread, f) 
   &*& [f]og->size |-> N &*&  [f]ConcurrentStructure_mutex(og, l) 
   &*& combined_ctr_locked(og, N)();  @*/

/* Wrapper for the mutex function release in threading.h */
void release(struct ConcurrentStructure *og);
/*@ requires [?f]og->mutex |-> ?l   &*& [f]og->size |-> ?N &*& mutex_held(l, combined_ctr(og, N), currentThread, f)
 &*& combined_ctr_release(og, N)(); @*/
//@ ensures [f]mutex(l, combined_ctr(og, N)) &*& [f]og->size |-> N &*& [f]ConcurrentStructure_mutex(og, l); 


/*  Wrapper for ConcurrentStructure permissions and mutex predicate */ 
/*@ 
predicate owicki_gries_inv(int noOfClients, struct ConcurrentStructure *og) ;

/* simple mathematical lemma needed for pointer Arithematic */
lemma void less_than_eq(int a, int b, int c);
    requires a >= 2 &*& c < a;
    ensures b <= a*b - c*b;
@*/

/*    Trace Manager struct that is handed to each
      participant to manipulate the global trace via the concurrent data structure  
*/

struct TraceManager *create_trace_managers(int noOfClients, list<Term> root_terms);
//@ requires 2 <= noOfClients &*& PublicInv(root_terms, root(root_terms)) == true;  

/*@ ensures malloc_block_ConcurrentStructure(?og) &*& og->mutex |-> ?l &*& 
    mutex(l, combined_ctr(og, noOfClients)) &*& og->size |-> noOfClients &*& 
    [1/2]og->snapshots |-> ?snap &*& malloc_block_chars((void *)result, (noOfClients * sizeof(struct TraceManager)))
    &*& snapshot_perm_forall(snap); @*/

#endif
