#ifndef GHOST_TRACE_H
#define GHOST_TRACE_H
#include "definitions.h"
/*@
fixpoint int getEventType<t>(EventADT<t> e){
  switch(e){
  case newEvent(type, params) : return type;
  }
}

fixpoint t getEventParams<t>(EventADT<t> e){
  switch(e){
  case newEvent(type, params) : return params;
  }
}

/* The next set of function provide a unique resource for a each nonce. 
   getCellId() gives an integer and nonceUniqueResource() says that 
   there is a ghost_cell with that integer */
fixpoint int getCellId(Term t);

predicate nonceUniqueResource(Term t) = 
  ghost_cell(getCellId(t), _);
/*----------------------EVENT PREDICATES--------------------*/

/* The next set of functions ensure that every unique event has 
   full permission to a resource. */
   
fixpoint int getCellIdEvent(Term witness, int type);

fixpoint bool eventConsistency(EventParams t, int type) CONSISTENCY

/* Client should give this fixpoint a body which 
   is the event predicate */ 
fixpoint bool  event_pure_pred(EventADT<EventParams> e, int principal, trace<EventParams> tr) EVENT_PRED
fixpoint bool isUnique(int type) UNIQUE


/* protocol implementations have to provide an implementation for this 
   function to map (the parameters of) each event to a particular uniqueness witness, 
   which is typically one of the event parameters */
fixpoint Term eventUniquenessWitness<t>(EventADT<t> e) UNIQUE_WITNESS



predicate EventUniqueResource<t>(Term nonce, int type) = 
 isUnique(type) ? ghost_cell(getCellIdEvent(nonce, type), _) : true;


/* Event predicate which says that the pure event fixpoint is true, and
   if the event is unique, then there is a unique resource for this event type. */
predicate event_pred(int principal, EventADT<EventParams> e, trace<EventParams> tr) = 
switch(e){
 case newEvent(type, params) : return event_pure_pred(e, principal, tr) == true &*& EventUniqueResource(eventUniquenessWitness(e), type) ;
};


fixpoint int trace_length<t>(trace<EventParams> t) {
    switch (t) {
        case root(root_terms) : return 1;
        case makeEvent(t0, p, e): return 1 + trace_length(t0);
        case makeCorrupt(t0, id) : return 1 + trace_length(t0);
        case makeMessage(t0,to,from,term) : return 1 + trace_length(t0);
        case makeDropMessage(t0, to, from, term) : return 1 + trace_length(t0);
        case makeNonce(t0, term, l)  : return 1 + trace_length(t0);
        case makePublic(t0, term) : return 1 + trace_length(t0);
    }
}





/*-- Takes 2 traces and returns true, if tr is the suffix of tr2 */
fixpoint bool individual_snapshot_suffix<t>(trace<EventParams> tr2, trace<EventParams> tr ){
      switch (tr) {
      case root(root_terms) : return tr == tr2 ?  true :  false; 
      case makeEvent(t0, pr, e): return tr == tr2 ?  true :  individual_snapshot_suffix(tr2, t0);
      case makeCorrupt(t0, id) : return tr == tr2 ?  true :   individual_snapshot_suffix(tr2, t0);
      case makeMessage(t0,to,from,term) : return tr == tr2 ?  true :   individual_snapshot_suffix(tr2, t0);
      case makeDropMessage(t0, to, from, term) : return tr == tr2 ?  true :  individual_snapshot_suffix(tr2, t0);
      case makeNonce(t0, term, l)  : return tr == tr2 ?  true :   individual_snapshot_suffix(tr2, t0);
      case makePublic(t0, term) : return tr == tr2 ?  true :   individual_snapshot_suffix(tr2, t0);   
     }
}

/* This recursive predicate contains [1/2] permission to the ghost cell where a snapshot is stored
   for all snapshots and ensures that the id is a member of the list*/ 
predicate snapshot_perm_forall(list<int> snapshots) = 
     switch (snapshots) {
      case nil : return emp;
      case cons(x, xs) : return [1/2]ghost_cell<Trace>(x, ?y) &*& mem(x, snapshots)== true &*& snapshot_perm_forall(xs);
     }
;

/* This recursive predicate contains [1/2] permission to the ghost cell where a snapshot is stored
   and ensures that the snapshots is a suffix of the global trace, for all snapshots. 
 */ 
predicate snapshot_suffix_forall<t>(list<int> snapshots,  trace<EventParams> global_trace) = 
     switch (snapshots) {
      case nil : return true;
      case cons(x, xs) : return [1/2]ghost_cell(x, ?trace) &*& individual_snapshot_suffix(trace, global_trace) == true
     &*& snapshot_suffix_forall(xs, global_trace) &*& trace_length(trace) <= trace_length(global_trace);
     }
;

/* adding an event to global trace preserves suffix */
lemma void snapshot_suffix_hold_event(trace<EventParams> global_trace, list<int> snaps);
requires snapshot_suffix_forall(snaps, ?t) &*& global_trace == makeEvent(t, _,_);
ensures snapshot_suffix_forall(snaps, global_trace);

/* adding a message to global trace preserves suffix */
lemma void snapshot_suffix_hold_message(trace<EventParams> global_trace, list<int> snaps);
requires snapshot_suffix_forall(snaps, ?t) &*& global_trace == makeMessage(t, _,_,_);
ensures snapshot_suffix_forall(snaps, global_trace);

/* The suffix relation (individual_snapshot_suffix) is reflexive */
lemma void snapshot_reflexive<t>(trace<EventParams> t1);
requires true;
ensures  individual_snapshot_suffix(t1, t1) == true;

/* The suffix relation (individual_snapshot_suffix)  is transitive */
lemma void snapshot_transitive<t>(trace<EventParams> t1, trace<EventParams> t2, trace<EventParams> t3);
requires individual_snapshot_suffix(t1, t2) && individual_snapshot_suffix(t2, t3);
ensures  individual_snapshot_suffix(t1, t3) == true;


lemma void snapshot_suffix_hold_adding_message<t>(trace<EventParams> t1, trace<EventParams> bigger) ;
requires bigger == makeMessage(t1, _,_,_);
ensures individual_snapshot_suffix(t1, bigger) == true;



lemma void snapshot_suffix_hold_nonce<t>(trace<EventParams> global_trace, list<int> snaps);
requires snapshot_suffix_forall(snaps, ?t) &*& global_trace == makeNonce(t, _,_);
ensures snapshot_suffix_forall(snaps, global_trace);


@*/
#endif

