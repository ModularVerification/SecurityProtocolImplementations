#ifndef INV_FINDER
#define INV_FINDER
#include "terms.h"
#include "trace_manager.h"
#include "crypto_lib.h"
#define optiontype option<int>
//@ #include "ghost_cells.gh"

/* This module extract invariants from the valid trace predicate 
   for specific terms 
*/

/*@

/* Returns true if there is a message from a given sender with a given payload */
fixpoint bool senderOccursWithTerm(trace<EventParams> tr,  int from, Term t){

switch (tr) {
      case root(root_terms) : return false;
      case makeEvent(t0, pr, e): return senderOccursWithTerm(t0, from, t);
      case makeCorrupt(t0, id) : return   senderOccursWithTerm(t0, from, t);
      case makeMessage(t0,to1,from1,term) : return (from1 == from && t == term) ?  true : senderOccursWithTerm(t0, from, t);
      case makeDropMessage(t0, to1, from1, term) :  return senderOccursWithTerm(t0, from, t);
      case makeNonce(t0, term, l)  : return senderOccursWithTerm(t0, from, t);
      case makePublic(t0, term) : return senderOccursWithTerm(t0, from, t);
      }
 }
 /* Returns true if there is a message from a given Receiver with a given payload */
fixpoint bool receiverOccursWithTerm(trace<EventParams> tr, int to, Term t){

switch (tr) {
      case root(root_terms) : return false;
      case makeEvent(t0, pr, e): return receiverOccursWithTerm(t0, to, t);
      case makeCorrupt(t0, id) : return   receiverOccursWithTerm(t0, to, t);
      case makeMessage(t0,to1,from1,term): return  to1 == to && term == t ?  true :receiverOccursWithTerm(t0, to, t);
      case makeDropMessage(t0, to1, from1, term) :  return receiverOccursWithTerm(t0, to, t);
      case makeNonce(t0, term, l)  : return receiverOccursWithTerm(t0, to, t);
      case makePublic(t0, term) : return receiverOccursWithTerm(t0, to, t);
     }
 
}
/*------TODO: Prove this lemma ------------------*/
/* This lemma states if terms is on the trace as a payload, and is not the current message, 
   then the term must be on the rest of the trace 
*/
lemma void messagePayloadsMemLemma(trace<EventParams> tr, trace<EventParams> tr0, Term mTerm, Term term, int to, int from);
requires mem(mTerm, getMessagePayloads(tr, nil)) == true &*& tr == makeMessage(tr0,to,from,term)
&*& mTerm != term;
ensures mem(mTerm, getMessagePayloads(tr0, nil)) == true;

/* Get a sender and Receiver for a given payload and prove that such a message exists */
lemma pair<int,int> getMessageSenderReceiver(trace<EventParams> tr, Term mTerm);
requires mem(mTerm, getMessagePayloads(tr, nil)) == true;
ensures  msgOccurs(mTerm, fst(result), snd(result), tr) == true;

/* Returns the sender of a message with a given payload */
lemma int getMessageSender(trace<EventParams> tr, Term mTerm);
requires mem(mTerm, getMessagePayloads(tr, nil)) == true;
ensures  senderOccurs(tr, result) == true;

/* Returns the Receiver of a message with a given payload */
lemma int getMessageReceiver(trace<EventParams> tr, Term mTerm);
requires mem(mTerm, getMessagePayloads(tr, nil)) == true;
ensures  receiverOccurs(tr, result) == true;


/*--- Get Public Terms on trace ---*/
fixpoint list<Term> getTermsMadePublic(trace<EventParams>tr, list<Term> pTerms) {
     switch (tr) {
      case root(root_terms) : return pTerms; 
      case makeEvent(t0, pr, e): return  getTermsMadePublic(t0, pTerms);
      case makeCorrupt(t0, id) : return getTermsMadePublic(t0, pTerms);
      case makeMessage(t0,to,from,term) :return getTermsMadePublic(t0, pTerms);
      case makeDropMessage(t0, to, from, term) : return getTermsMadePublic(t0, pTerms);
      case makeNonce(t0, term, l)  : return getTermsMadePublic(t0, pTerms);
      case makePublic(t0, term) : return getTermsMadePublic(t0, cons(term, pTerms));
     }
}

/*--- Returns true if a term has been made Public ---*/
fixpoint bool termOccursPublic(Term t, trace<EventParams> tr){

     switch (tr) {
      case root(root_terms) : return false; 
      case makeEvent(t0, pr, e): return termOccursPublic(t, t0);
      case makeCorrupt(t0, id) : return termOccursPublic(t, t0);
      case makeMessage(t0,to,from,term) :return termOccursPublic(t, t0);
      case makeDropMessage(t0, to, from, term) : return termOccursPublic(t, t0);
      case makeNonce(t0, term, l)  : return termOccursPublic(t, t0);
      case makePublic(t0, term) : return (term == t) ? true : termOccursPublic(t, t0);
     }

}

/*----------- TODO: PROVE THIS ------------*/
lemma void termOccursPublicLemma(Term t, trace<EventParams> tr);
requires mem(t, getTermsMadePublic(tr, nil)) == true;
ensures termOccursPublic(t, tr) == true;

/*--- All the terms the attacker knows ---*/
fixpoint list<Term> attackerKnowledge(trace<EventParams> tr){
  return append (append(getTermsMadePublic(tr, nil), getMessagePayloads(tr, nil)), getPublicTerms(tr));
}

/*---- returns true if the attacker knows the term ----*/
fixpoint bool attackerKnows<t>(trace<EventParams> tr, Term term)  {
    return mem(term, attackerKnowledge(tr));
}



/*------------ Extract Public Invariants --------------*/
lemma void getPublicInv(trace<EventParams> global_trace, trace<EventParams> snapshot);
requires valid_trace(global_trace) &*& individual_snapshot_suffix(snapshot, global_trace) == true;
ensures valid_trace(global_trace) &*& PublicInv(getPublicTerms(snapshot), root(getPublicTerms(snapshot))) == true;


/*------------ Wrapper Function for extracting Public Invariants --------------*/
lemma void getPublicInvWrapper(trace<EventParams> global_trace, list<int> snap, int x);
requires [1/2]ghost_cell<Trace>(x, ?snapshot)  &*& 
  mem(x, snap) == true &*& distinct(snap) == true   &*&  
  ghost_cell<Trace>(?id, global_trace) &*& valid_trace(global_trace)
  &*&   snapshot_suffix_forall(snap,global_trace);
ensures [1/2]ghost_cell<Trace>(x, snapshot)  &*& 
  mem(x, snap) == true &*& distinct(snap) == true   &*&  ghost_cell<Trace>(id, global_trace) &*& valid_trace(global_trace)
  &*&   snapshot_suffix_forall(snap,global_trace) &*& PublicInv(getPublicTerms(snapshot), root(getPublicTerms(snapshot))) == true; 


/*------- Extract Message Invariant ---------*/
lemma trace<EventParams> getMsgInv(trace<EventParams> global_trace, trace<EventParams> snapshot, int to, int from, Term t);
requires valid_trace(global_trace) &*& individual_snapshot_suffix(snapshot, global_trace) == true 
&*& msgOccurs(t, to, from, snapshot) == true;
ensures valid_trace(global_trace) &*& isPublishable(result, t, pkePred) == true
        &*& individual_snapshot_suffix(result, snapshot) == true;


lemma trace<EventParams> getMsgInvWrapper(trace<EventParams> global_trace, list<int> snap, trace<EventParams> given_snap, int x, Term term, int to, int from);
requires [1/2]ghost_cell<Trace>(x, ?snapshot)  &*& 
  mem(x, snap) == true &*& distinct(snap) == true   &*&  
  ghost_cell<Trace>(?id, global_trace) &*& valid_trace(global_trace)
  &*&   snapshot_suffix_forall(snap,global_trace) &*&   msgOccurs(term, to, from, given_snap) == true
  &*&  individual_snapshot_suffix(given_snap, snapshot) == true;
ensures [1/2]ghost_cell<Trace>(x, snapshot)  &*& 
  mem(x, snap) == true &*& distinct(snap) == true   &*&  ghost_cell<Trace>(id, global_trace) &*& valid_trace(global_trace)
  &*&   snapshot_suffix_forall(snap,global_trace) &*& isPublishable(result, term, pkePred) == true
  &*& individual_snapshot_suffix(result, given_snap) == true &*& trace_length(result) <= trace_length(global_trace); 


/*------- Extract Public Invariant for Public Terms ---------*/
lemma trace<EventParams> getPublicTermsInv(trace<EventParams> global_trace, trace<EventParams> snapshot, Term t);
requires valid_trace(global_trace) &*& individual_snapshot_suffix(snapshot, global_trace) == true 
&*& termOccursPublic(t, snapshot) == true;

ensures valid_trace(global_trace) &*& isPublishable(result, t, pkePred) == true
        &*& individual_snapshot_suffix(result, snapshot) == true;




lemma trace<EventParams> getPublicTermsWrapper(trace<EventParams> global_trace, list<int> snap, trace<EventParams> given_snap, int x, Term term);
requires [1/2]ghost_cell<Trace>(x, ?snapshot)  &*& 
  mem(x, snap) == true &*& distinct(snap) == true   &*&  
  ghost_cell<Trace>(?id, global_trace) &*& valid_trace(global_trace)
  &*&   snapshot_suffix_forall(snap,global_trace) &*&   termOccursPublic(term, given_snap) == true
  &*&  individual_snapshot_suffix(given_snap, snapshot) == true;
ensures [1/2]ghost_cell<Trace>(x, snapshot)  &*& 
  mem(x, snap) == true &*& distinct(snap) == true   &*&  ghost_cell<Trace>(id, global_trace) &*& valid_trace(global_trace)
  &*& snapshot_suffix_forall(snap,global_trace) 
  &*& individual_snapshot_suffix(result, given_snap) == true
  &*& termOccursPublic(term, given_snap) == true
  &*& isPublishable(result, term, pkePred) == true
  &*& trace_length(result) <= trace_length(global_trace); 

/*---------------Retrieve Public Terms Inv ------------------*/
@*/
void findEntryWithPurePublicInvWithSnap(trace<EventParams> snap, int noOfClients, struct TraceManager *tm, Term term);
/*@ requires [1/2]ghost_cell<Trace>(?x, ?snapshot) &*& TraceManagerMem(tm, noOfClients, x) &*& 
    individual_snapshot_suffix(snap, snapshot) == true &*& mem(term, getPublicTerms(snap)) == true;
    @*/
/*@     ensures [1/2]ghost_cell<Trace>(x, snapshot) &*& TraceManagerMem(tm, noOfClients, x) &*& 
        mem(term, getPublicTerms(snap)) == true
        &*& individual_snapshot_suffix(snap, snapshot) == true 
        &*& PublicInv(getPublicTerms(snap), root(getPublicTerms(snap))) == true;
@*/

trace<EventParams> PublicTermImpliesPublicInvWithSnap(struct TraceManager *tm, int noOfClients, trace<EventParams> snap, Term term);
/*@ requires  [1/2]ghost_cell<Trace>(?x, ?snapshot) &*& TraceManagerMem(tm, noOfClients, x) &*& 
    individual_snapshot_suffix(snap, snapshot) == true &*& mem(term, getPublicTerms(snap)) == true;@*/
    
/*@ ensures [1/2]ghost_cell<Trace>(x, snapshot) &*& TraceManagerMem(tm, noOfClients, x) &*&
     individual_snapshot_suffix(result, snap) == true &*& PublicInv(getPublicTerms(snap), result) == true
    &*& individual_snapshot_suffix(result, snap) == true; @*/


/*---------------Retrieve Message Terms Inv ------------------*/


void findEntryWithPureMsgInvWithSnap(trace<EventParams> snap, int noOfClients, struct TraceManager *tm, Term term);
/*@ requires [1/2]ghost_cell<Trace>(?x, ?snapshot) &*& TraceManagerMem(tm, noOfClients, x) &*& 
    individual_snapshot_suffix(snap, snapshot) == true &*&   ghost_cell(?id1, ?from) &*& ghost_cell(?id2, ?to) &*&
    msgOccurs(term, to, from, snap) == true;
@*/
/*@     ensures [1/2]ghost_cell<Trace>(x, snapshot) &*& TraceManagerMem(tm, noOfClients, x) &*& 
         ghost_cell(id1, from) &*& ghost_cell(id2, to) &*&
        ghost_cell<Trace>(?id,?result) &*& individual_snapshot_suffix(result, snap) == true &*&
        individual_snapshot_suffix(snap, snapshot) == true &*&  isPublishable(result, term, pkePred) == true
    ;
@*/


void PublicTermImpliesMsgInvWithSnap(struct TraceManager *tm, int noOfClients, trace<EventParams> snap, Term term);
/*@ requires  [1/2]ghost_cell<Trace>(?x, ?snapshot) &*& TraceManagerMem(tm, noOfClients, x) &*& 
    ghost_cell(?id1, ?from) &*& ghost_cell(?id2, ?to) &*&
    individual_snapshot_suffix(snap, snapshot) == true &*& mem(term, getMessagePayloads(snap, nil)) == true
    &*& msgOccurs(term, to, from, snap) == true;@*/
    
/*@ ensures [1/2]ghost_cell<Trace>(x, snapshot) &*& TraceManagerMem(tm, noOfClients, x) &*&
      ghost_cell<Trace>(?id,?result) &*&  
      ghost_cell(id1, from) &*& ghost_cell(id2, to) &*&
      individual_snapshot_suffix(result, snap) == true 
      &*& individual_snapshot_suffix(result, snap) == true &*&
      individual_snapshot_suffix(snap, snapshot) == true &*& 
      isPublishable(result, term, pkePred) == true;
        @*/

void madePublicTermImpliesPublishableSnap(struct TraceManager *tm, int noOfClients, trace<EventParams> snap, Term term);
/*@ requires  [1/2]ghost_cell<Trace>(?x, ?snapshot) &*& TraceManagerMem(tm, noOfClients, x) &*& 
    individual_snapshot_suffix(snap, snapshot) == true &*& mem(term, getTermsMadePublic(snap, nil)) == true
    &*& termOccursPublic(term, snap) == true;@*/
    
/*@ ensures [1/2]ghost_cell<Trace>(x, snapshot) &*& TraceManagerMem(tm, noOfClients, x) &*&
      ghost_cell<Trace>(?id,?result) &*&  
          individual_snapshot_suffix(result, snap) == true 
            &*& individual_snapshot_suffix(result, snap) == true &*&
            individual_snapshot_suffix(snap, snapshot) == true &*& 
            isPublishable(result, term, pkePred) == true;
        @*/



/*@ lemma void getPublishableFromPublicInv(Term t, list<Term> root_terms, trace<EventParams> tr);
requires PublicInv(root_terms, tr) == true &*& mem(t, root_terms) == true;
ensures isPublishable(tr, t, pkePred) == true; 

@*/