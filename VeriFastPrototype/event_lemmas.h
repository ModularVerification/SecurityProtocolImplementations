#ifndef EVENT_LEMMAS_H
#define EVENT_LEMMAS_H
#include "ghost_trace.h"
#include "terms.h"

/* This module proves important lemmas about events. Most importantly, 
   we prove the UniqueEventsAreUnique lemma, which shows that there if a 
   event is unique, there is only one of it on the trace 
*/


/*@

fixpoint bool isNonce(Term t){
  switch(t){
    case IntConstant(value): return false;
    case StringConstant(str): return false;
    case EncryptedTerm(pk, plaintext): return false;
    case Hash(ht): return false;
    case PublicKey(str_k) :   return false;
    case Nonce(nonce_term, l) : return true; 
    case TwoTuple(Term1, Term2):  return   false;
    case ThreeTuple(Term1, Term2, Term3):  return false;
    case FourTuple(Term1, Term2, Term3, Term4):  return false;

  }
}




lemma void eventIsContradictionHelper(EventADT<EventParams> e1, EventADT<EventParams> e2, int principal1, int principal2, trace<EventParams> tr);
requires   eventOccurs(tr, principal2, e2) == true &*& 
eventUniquenessWitness((e1)) == eventUniquenessWitness((e2)) &*& isUnique(getEventType(e1)) == true
&*& getEventType(e1) == getEventType(e2) &*& valid_trace(tr) &*& event_pred(principal1, e1, tr);  
ensures principal1 == principal2 &*& e1 == e2 &*& valid_trace(tr);

lemma void eventOnTraceImpliesEventPred(EventADT<EventParams> e1, EventADT<EventParams> e2, int principal1, int principal2, trace<EventParams> tr);
requires eventOccurs(tr, principal1, e1) == true &*& eventOccurs(tr, principal2, e2) == true &*& 
eventUniquenessWitness((e1)) == eventUniquenessWitness((e2)) &*& isUnique(getEventType(e1)) == true
&*& getEventType(e1) == getEventType(e2) &*& valid_trace(tr); 
ensures principal1 == principal2 &*& e1 == e2 &*& valid_trace(tr);


lemma void UniqueEventsAreUnique(trace<EventParams> suffix, trace<EventParams> global_trace, int principal1, int principal2, EventADT<EventParams> e1, EventADT<EventParams> e2);
requires individual_snapshot_suffix(suffix, global_trace) == true &*& valid_trace(global_trace) &*& 
eventOccurs(suffix, principal1, e1) == true &*& eventOccurs(suffix, principal2, e2) == true &*& 
eventUniquenessWitness((e1)) == eventUniquenessWitness((e2)) &*& isUnique(getEventType(e1)) == true
&*& getEventType(e1) == getEventType(e2);
ensures principal1 == principal2 &*& e1 == e2 &*& valid_trace(global_trace);

@*/

#endif