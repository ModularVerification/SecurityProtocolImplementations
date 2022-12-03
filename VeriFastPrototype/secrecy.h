#ifndef SECRECY
#define SECRECY
#include "inv_finder.h"
#include "terms.h"
#include "ghost_trace.h"

//@ #include "ghost_cells.gh"

/*   
      The lemmas in this module prove the secrecy lemma. This is an important 
      security property that states that either the attacker does not know a
      non-public, valid term or one of the readers of this term must have been corrupted.
*/

void AttackerOnlyKnowsPublishableValuesWithSnap(struct TraceManager *tm, int noOfClients, trace<EventParams> snap, Term term) ;
/*@requires [1/2]ghost_cell<Trace>(?x, ?snapshot) &*& TraceManagerMem(tm, noOfClients, x) &*& 
         attackerKnows(snap, term) == true &*& individual_snapshot_suffix(snap, snapshot) == true;
         @*/
/*@ ensures isPublishable(snap, term, pkePred) == true &*& [1/2]ghost_cell<Trace>(x, snapshot) &*& TraceManagerMem(tm, noOfClients, x);
@*/


/*@
fixpoint bool Secrecy<t>(Term term, trace<EventParams> snapshot, list<int> honestIds){
   return  isValid(snapshot, term, pkePred) && (getLabel(term) == Readers(honestIds)
   && !attackerKnows(snapshot, term)) || containsCorruptId(getCorruptIds(snapshot), honestIds);
  }
@*/

void secrecyHelper(Term term, Trace snapshot, list<int> readers,int noOfClients,  struct TraceManager *tm);
/*@ requires  [1/2]ghost_cell<Trace>(?x, snapshot) &*& TraceManagerMem(tm, noOfClients, x) &*& 
isValid(snapshot, term, pkePred) && getLabel(term) == Readers(readers) &*& length(readers) > 0 
&*& attackerKnows(snapshot, term) == true;
@*/
/*@
ensures  [1/2]ghost_cell<Trace>(x, snapshot) &*& (Secrecy(term, snapshot, readers) == true
       &*& ghost_cell<optiontype>(?id, ?result) &*& (
       switch(result){
       case some(y): return mem(y, getCorruptIds(snapshot))
       && mem(y, readers); case none: return !attackerKnows(snapshot, term) ;})
       &*& TraceManagerMem(tm, noOfClients, x));
       @*/



void SecrecyLemma<t>(Term term, list<int> readers, int noOfClients,  struct TraceManager *tm, Trace snapshot);
/*@requires [1/2]ghost_cell<Trace>(?x, snapshot) &*& TraceManagerMem(tm, noOfClients, x) 
&*& isValid(snapshot, term, pkePred)   
&& length(readers) > 0 &*& (getLabel(term) == Readers(readers))
|| containsCorruptId(getCorruptIds(snapshot), readers);@*/
/*@
ensures [1/2]ghost_cell<Trace>(x, snapshot) &*& (Secrecy(term, snapshot, readers) == true
       &*& ghost_cell<optiontype>(?id, ?result) &*& (
       switch(result){
       case some(y): return mem(y, getCorruptIds(snapshot))
       && mem(y, readers); case none: return !attackerKnows(snapshot, term) ;})
       &*& TraceManagerMem(tm, noOfClients, x));
       @*/
       


#endif
     