#ifndef TERMS
#define TERMS
#include "protocol_specific_lemmas.h"
#include "ghost_trace.h"
//@ #include "quantifiers.gh"

//@ #include "list.gh"


/*@

fixpoint Term createPk(Term t){
  return PublicKey(t);
}


fixpoint Term encrypt(Term pk, Term t){
  return EncryptedTerm(pk, t); 
}

/* get corrupted ids */
fixpoint list<int> getCorruptIds<t>(trace<EventParams> t){
     switch (t) {
        case root(root_terms) : return nil;
        case makeEvent(t0, p, e): return getCorruptIds(t0);
        case makeCorrupt(t0, id) : return cons(id, getCorruptIds(t0));
        case makeMessage(t0,to,from,term) : return getCorruptIds(t0);
        case makeDropMessage(t0, to, from, term) : return getCorruptIds(t0);
        case makeNonce(t0, term, l)  : return getCorruptIds(t0);
        case makePublic(t0, term) : return getCorruptIds(t0);
    }
} 

fixpoint bool containsCorruptId<t>(list<t> corruptIds, list<t> ids){
  return (intersection (corruptIds, ids)) != nil;
}

fixpoint bool containsIds<t>(list<t> haystack, list<t> ids){
  return subset(ids, haystack);
}

fixpoint bool canFlowInternal(Label l1, Label l2, list<int>corruptIds){
  switch (l1){
  case Public : return true;
  case Readers(l1_readers):  return switch (l2){
  				case Public :  return containsCorruptId(corruptIds, l1_readers);
  				case Readers(l2_readers): return containsCorruptId(corruptIds, l1_readers) || containsIds(l1_readers, l2_readers);
     };
  }
}

fixpoint bool canFlow<t>(trace<EventParams> t, Label l1, Label l2)
{
    return canFlowInternal(l1, l2, getCorruptIds(t));
}


lemma void canFlowInternalReflexive(Label l1,list<int>corruptIds);
requires true;
ensures canFlowInternal(l1, l1, corruptIds) == true;


lemma void canFlowReflexive<t>(Label l1, trace<EventParams> t);
requires true;
ensures canFlow(t, l1, l1) == true;

fixpoint Label getUnderspecifiedLabel(Term t);
/* Gets labels for a given term */
fixpoint Label getLabel(Term t)
{
 switch(t){
    case IntConstant(value): return Public;
    case StringConstant(str): return Public;
    case EncryptedTerm(pk, plaintext): return Public;
    case Hash(term): return Public;
    case PublicKey(str_k) :  return Public;
    case Nonce(term, l) : return l;
    case TwoTuple(Term1, Term2): return getUnderspecifiedLabel(t);
    case ThreeTuple(Term1, Term2, Term3): return getUnderspecifiedLabel(t);
    case FourTuple(Term1, Term2, Term3, Term4): return getUnderspecifiedLabel(t);
 }
} 
/* Gets the private key's label for a public key */
fixpoint Label getSkLabel(Term t){
   switch(t){
    case IntConstant(value): return Public;
    case StringConstant(str): return Public;
    case EncryptedTerm(pk, plaintext): return Public;
    case Hash(term): return Public;
    case PublicKey(str_k) :  return getLabel(str_k);
    case Nonce(term, l) : return Public;
    case TwoTuple(Term1, Term2): return Public;
    case ThreeTuple(Term1, Term2, Term3): return Public;
    case FourTuple(Term1, Term2, Term3, Term4): return Public;
 }
    
}

/* Returns true if nonceOccurs on the trace */
fixpoint bool nonceOccurs<t>(trace<EventParams> tr, Term t, Label l){
     switch (tr) {
      case root(root_terms) : return false; 
      case makeEvent(t0, pr, e): return nonceOccurs(t0, t, l);
      case makeCorrupt(t0, id) :  return nonceOccurs(t0, t, l);
      case makeMessage(t0,to,from,term): return nonceOccurs(t0, t, l);
      case makeDropMessage(t0, to, from, term) :  return nonceOccurs(t0, t, l);
      case makeNonce(t0, term, la): return (t == term && la == l) ?  true :  nonceOccurs(t0, t, l) ;
      case makePublic(t0, term) :  return nonceOccurs(t0, t, l);
     }
}

/* nonceOccurs is monotonic */
lemma void nonceOccursMonotonic<t>(trace<EventParams> t1, trace<EventParams> t2, Term t, Label l);
requires individual_snapshot_suffix(t1, t2) == true && nonceOccurs(t1, t, l) == true;
ensures nonceOccurs(t2, t, l) == true;


fixpoint bool eventOccurs(trace<EventParams> tr, int principal, EventADT<EventParams> e){
   switch(tr){
        case root(root_terms) : return false;
        case makeEvent(t0, p, eCurr): return (principal == p && e == eCurr) ? true :  eventOccurs(t0, principal, e);
        case makeCorrupt(t0, id) : return eventOccurs(t0, principal, e);
        case makeMessage(t0,to,from,term) : return eventOccurs(t0, principal, e);
        case makeDropMessage(t0, to, from, term) : return eventOccurs(t0, principal, e);
        case makeNonce(t0, term, l)  : return eventOccurs(t0, principal, e);
        case makePublic(t0, term) : return eventOccurs(t0, principal, e);
   
   }

} 


/*------------------isValid()-------------------*/
/* returns true if a Term is valid */
fixpoint bool isValid<t>(trace<EventParams> t, Term term, fixpoint (trace<EventParams>, Term, Term, bool) p){ 
  switch(term){
    case IntConstant(value): return true;
    case StringConstant(str): return true;
    case EncryptedTerm(pk, plaintext): return (isValid(t, pk, p) &&  isValid(t, plaintext, p) && 
                                            canFlow(t, getLabel(plaintext), getSkLabel(pk))
                                            &&(canFlow(t, getLabel(plaintext), Public)  ||
                                             p(t, plaintext, pk)));

    case Hash(ht): return isValid(t, ht, p);
    case PublicKey(pkeKey) :  return isValid(t, pkeKey, p);
    case Nonce(bytes, l) : return nonceOccurs(t,  Nonce(bytes, l), l); 
    case TwoTuple(Term1, Term2): return isValid(t, Term1, p) && isValid(t, Term2, p);
    case ThreeTuple(Term1, Term2, Term3): return isValid(t, Term1, p) && isValid(t, Term2, p) && isValid(t, Term3, p);
    case FourTuple(Term1, Term2, Term3, Term4): return isValid(t, Term1, p) && isValid(t, Term2, p) && isValid(t, Term3, p) && isValid(t, Term4, p);

 }
}

/*----------MESSAGE PREDICATES---------------*/

fixpoint bool isMsg<t>(trace<EventParams> t, Term term, Label label, fixpoint (trace<EventParams>, Term, Term, bool) p) {return  (isValid(t, term, p) && canFlow(t, getLabel(term), label));}
fixpoint bool isPublishable<t>(trace<EventParams> t, Term term, fixpoint (trace<EventParams>, Term, Term, bool) p){ return  isMsg(t, term, Public, p); } 

fixpoint bool messageInv<t>(int to, int from, Term term, trace<EventParams> t, fixpoint (trace<EventParams>, Term, Term, bool) p){return isPublishable(t, term, p); }

/*-------------------------------------------*/

fixpoint bool isLabeled(Term t, trace<EventParams> tr, Label l){
  return isValid(tr, t, pkePred) && getLabel(t) == l;
}



lemma void eventOccursMonotonic(trace<EventParams> t1, trace<EventParams> t2, int principal, EventADT<EventParams> e);
requires individual_snapshot_suffix(t1, t2) == true &*& eventOccurs(t1, principal, e) == true;
ensures eventOccurs(t2, principal, e) == true;


/*  getCorruptIds() function is monotonic */
// t2 is the larger one
lemma void getCorruptIdsMonotonic(trace<EventParams> t1, trace<EventParams> t2);
requires individual_snapshot_suffix(t1, t2) == true;
ensures subset(getCorruptIds(t1), getCorruptIds(t2)) == true;

//TODO: Prove this Lemma
lemma void subset_intersection_helper<t>(list<t> smaller, list<t> larger, list<t> aux);
requires intersection(smaller, aux) != nil && subset(smaller, larger);
ensures intersection(larger, aux) != nil;

/*----- Monotonicity of the various parts of the Message Invariant ------*/
lemma void canFlowInternalMonotonic<t>(trace<EventParams> t1, trace<EventParams> t2, Label l1, Label l2);
requires individual_snapshot_suffix(t1, t2) == true && canFlow(t1, l1, l2) == true;
ensures canFlow(t2, l1, l2) == true;



lemma void isValidMonotonic(trace<EventParams> t1, trace<EventParams> t2, Term term, fixpoint (trace<EventParams>, Term, Term, bool) p);
requires individual_snapshot_suffix(t1, t2) == true &*& isValid(t1, term, p) == true &*& p == pkePred;
ensures isValid(t2, term, p) == true;


lemma void isMsgMonotonic(trace<EventParams> t1, trace<EventParams> t2, Term term, Label label, fixpoint (trace<EventParams>, Term, Term, bool) p);
requires individual_snapshot_suffix(t1, t2) == true &*& isMsg(t1, term, label, p) == true &*& p == pkePred;
ensures isMsg(t2, term, label, p) == true ;


lemma void isPublishableMonotonic<t>(trace<EventParams> t1, trace<EventParams> t2, Term term, fixpoint (trace<EventParams>, Term, Term, bool) p);
requires individual_snapshot_suffix(t1, t2) == true &*& isPublishable(t1, term, p) == true &*& p == pkePred;
ensures isPublishable(t2, term, p) == true ;

lemma void messageInvMonotonic<t>(trace<EventParams> t1, trace<EventParams> t2, int to, int from, Term term,  fixpoint (trace<EventParams> t, Term, Term, bool)  p);
requires individual_snapshot_suffix(t1, t2) == true &*& messageInv(to, from, term,t1, p) == true &*& p == pkePred ;
ensures messageInv(to, from, term,t2, p) == true;

/*----- Public Term Invariants -----*/
fixpoint bool madePublicInv(trace<EventParams> tr,  Term term)  {
    return isPublishable(tr, term, pkePred);
}

fixpoint bool PublicInv(list<Term> root_terms, trace<EventParams> y){ 
    switch(root_terms){
    case nil: return true;
    case cons(x, xs): return isPublishable(y, x, pkePred) && PublicInv(xs, y);
    
    }
   }

/*--- valid trace predicate ---*/
predicate valid_trace(trace<EventParams>  tr) = 
      switch (tr) {
      case root(root_terms) : return PublicInv(root_terms, root(root_terms)) == true; 
      case makeEvent(t0, pr, e): return  event_pred(pr, e, t0) &*& valid_trace(t0);
      case makeCorrupt(t0, id) : return  valid_trace(t0);
      case makeMessage(t0,to,from,term) :return messageInv(to, from, term, t0, pkePred) == true &*& valid_trace(t0);
      case makeDropMessage(t0, to, from, term) : return messageInv(to, from, term, t0, pkePred) == true  &*&  valid_trace(t0);
      case makeNonce(t0, term, l)  : return ghost_cell(getCellId(term), _) &*& valid_trace(t0);
      case makePublic(t0, term) : return madePublicInv(t0, term) == true &*& valid_trace(t0) ;
     }; 



/*--- lemma that proves that 2 full permissions to the same cell is a contradiction */
lemma void noncePointerIsUniqueContradiction(int x, int y);
requires ghost_cell(x, _) &*& ghost_cell(y, _) &*& x == y;
ensures false;


/* returns true if a given nonce is at index i of the trace */ 
fixpoint bool nonceAt(trace<EventParams> tr, Term t, Label l, int i){
     switch (tr) {
      case root(root_terms) : return false; 
      case makeEvent(t0, pr, e): return nonceAt(t0, t, l,  i);
      case makeCorrupt(t0, id) :  return nonceAt(t0, t, l,  i);
      case makeMessage(t0,to,from,term): return nonceAt(t0, t, l,  i);
      case makeDropMessage(t0, to, from, term) :  return nonceAt(t0, t, l,  i);
      case makeNonce(t0, term, la): return (t == term && la == l) ?  trace_length(tr) == i ? true : nonceAt(t0, t, l, i)  :  nonceAt(t0, t, l, i) ;
      case makePublic(t0, term) :  return nonceAt(t0, t, l, i);
     }
}



lemma void nonceUnique(trace<EventParams> tr, Term t, Label l, int i, int j);
requires valid_trace(tr) &*& nonceAt(tr, t, l, i) == true &*& nonceAt(tr, t, l, j) == true;
ensures i == j &*& valid_trace(tr); 


/* Returns true if a msgOccurs on the trace */
fixpoint bool msgOccurs(Term t, int to, int from,trace<EventParams> tr){

switch (tr) {
      case root(root_terms) : return false;
      case makeEvent(t0, pr, e): return msgOccurs(t, to, from, t0);
      case makeCorrupt(t0, id) : return   msgOccurs(t, to, from, t0);
      case makeMessage(t0,to1,from1,term) : return t == term && to1 == to && from1 == from ?  true :  msgOccurs(t, to, from, t0);
      case makeDropMessage(t0, to1, from1, term) :  return msgOccurs(t, to, from, t0);
      case makeNonce(t0, term, l)  : return msgOccurs(t, to, from, t0);
      case makePublic(t0, term) : return msgOccurs(t, to, from, t0);
     }
 }

/*---- gets the public terms that were given at initialization ----*/
fixpoint list<Term> getPublicTerms<t>(trace<EventParams> tr){
   switch (tr) {
      case root(root_terms) : return root_terms; 
      case makeEvent(t0, pr, e): return  getPublicTerms(t0);
      case makeCorrupt(t0, id) : return getPublicTerms(t0);
      case makeMessage(t0,to,from,term) :return getPublicTerms(t0);
      case makeDropMessage(t0, to, from, term) : return getPublicTerms(t0);
      case makeNonce(t0, term, l)  : return getPublicTerms(t0);
      case makePublic(t0, term) : return getPublicTerms(t0);
     }
}

/*---- Returns true if a message with a given sender occurs */
fixpoint bool senderOccurs<t>(trace<EventParams> tr,  int from){

switch (tr) {
      case root(root_terms) : return false;
      case makeEvent(t0, pr, e): return senderOccurs(t0, from);
      case makeCorrupt(t0, id) : return   senderOccurs(t0, from);
      case makeMessage(t0,to1,from1,term) : return from1 == from ?  true :  senderOccurs(t0, from);
      case makeDropMessage(t0, to1, from1, term) :  return senderOccurs(t0, from);
      case makeNonce(t0, term, l)  : return senderOccurs(t0, from);
      case makePublic(t0, term) : return senderOccurs(t0, from);
      }
 }

/*---- Returns true if a message with a given receiver occurs */
fixpoint bool receiverOccurs<t>(trace<EventParams> tr, int to){

switch (tr) {
      case root(root_terms) : return false;
      case makeEvent(t0, pr, e): return receiverOccurs(t0, to);
      case makeCorrupt(t0, id) : return   receiverOccurs(t0, to);
      case makeMessage(t0,to1,from1,term): return  to1 == to ?  true : receiverOccurs(t0, to);
      case makeDropMessage(t0, to1, from1, term) :  return receiverOccurs(t0, to);
      case makeNonce(t0, term, l)  : return receiverOccurs(t0, to);
      case makePublic(t0, term) : return receiverOccurs(t0, to);
     }
 }

/*-- Get all the message Terms in a list */
fixpoint list<Term> getMessagePayloads<t>(trace<EventParams> tr, list<Term> pTerms)

{
   switch (tr) {
      case root(root_terms) : return reverse(pTerms); 
      case makeEvent(t0, pr, e): return  getMessagePayloads(t0, pTerms);
      case makeCorrupt(t0, id) : return getMessagePayloads(t0, pTerms);
      case makeMessage(t0,to,from,term) : return getMessagePayloads(t0, cons(term, pTerms));
      case makeDropMessage(t0, to, from, term) : return getMessagePayloads(t0, pTerms);
      case makeNonce(t0, term, l)  : return getMessagePayloads(t0, pTerms);
      case makePublic(t0, term) : return getMessagePayloads(t0, pTerms);
     }
}


/*---- a few more monotoncity lemmas ----*/
lemma void rootIsSuffix<t>(trace<EventParams> tr, trace<EventParams> r);
requires r == root(getPublicTerms(tr));
ensures individual_snapshot_suffix(r, tr) == true;


lemma void getPublicTermsMonotonic<t>(trace<EventParams> t1, trace<EventParams> t2);
requires individual_snapshot_suffix(t1, t2) == true;
ensures getPublicTerms(t1) == getPublicTerms(t2);

lemma void msgOccursMonotonic<t>(Term t, int to, int from, trace<EventParams> tr, trace<EventParams> global_trace);
requires individual_snapshot_suffix(tr, global_trace) && msgOccurs(t, to, from, tr);
ensures msgOccurs(t, to, from, global_trace) == true;


// TODO PROVE THIS
lemma void eventPredMonotonic<t>(trace<EventParams> t1, trace<EventParams> t2, int principal, EventADT<EventParams> e);
requires individual_snapshot_suffix(t1, t2) == true &*& event_pred(principal, e, t1);
ensures event_pred(principal, e, t2);

          
fixpoint bool isSecret(trace<EventParams> tr, Term term, Label l) {
  return isLabeled(term, tr, l);
}
fixpoint bool isPrivateDecKey(trace<EventParams> tr, int owner, Term sk){
 return isSecret(tr, sk, Readers(cons(owner, nil)));
}

fixpoint bool isSecretKey(trace<EventParams> tr, int owner, Term sk, int keyType){
 return (keyType == 1) ? isPrivateDecKey(tr, owner, sk) :  false;
}

fixpoint bool isPublicEncKey(trace<EventParams> tr, int owner, Term pk,  Term sk, int keyType) {
    return isPublishable(tr, pk, pkePred) &&
        isPrivateDecKey(tr, owner, sk) &&
        pk == createPk(sk);
}

fixpoint bool isPublicKey(trace<EventParams> tr, int owner, Term pk, Term sk, int keyType){
 return (keyType == 1) ? isPublicEncKey(tr, owner, pk, sk, keyType) :  false;
}
@*/
#endif 
