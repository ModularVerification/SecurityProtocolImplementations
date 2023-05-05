#ifndef CRYPT
#define CRYPT
#include "ghost_trace.h"
#include "terms.h"
#include "gamma.h"

/*----- This module contains some lemmas related to encryption and encrypted term -----*/
/*@
fixpoint pair<bool,Term> getPrivateKey(Term pk){
    switch(pk){
    case IntConstant(value): return pair(false, pk);
    case StringConstant(str): return  pair(false, pk);
    case EncryptedTerm(x, y): return  pair(false, pk);
    case Hash(ht):return  pair(false, pk);
    case PublicKey(pkeKey) :  return  pair(true, pkeKey);
    case Nonce(bytes, l) : return  pair(false, pk);
    case TwoTuple(Term1, Term2):  return  pair(false, pk);
    case ThreeTuple(Term1, Term2, Term3):  return  pair(false, pk);
    case FourTuple(Term1, Term2, Term3, Term4):  return   pair(false, pk);
     }
}


fixpoint bool canEncrypt(trace<EventParams> t, Term msg, int to, int from, Term pk){

 return pkePred(t, msg, ((pk)))
  &&  (isPublishable(t, pk, pkePred) && isMsg(t, msg, getSkLabel(pk), pkePred));

  
}

fixpoint bool canDecrypt(trace<EventParams> tr, Term ciphertext, Term sk, int owner){
  return  (isValid(tr, sk, pkePred)) && getLabel(sk) ==  Readers(cons(owner, nil)) 
  && isPublishable(tr, ciphertext, pkePred)
   && (isPublishable(tr, sk, pkePred) || isPrivateDecKey(tr, owner, sk));
   
}

lemma void canFlowTransitive(trace<EventParams> tr, Label l1, Label l2, Label l3);
requires canFlow(tr, l1, l2) == true &*& canFlow(tr, l2, l3) == true; 
ensures canFlow(tr, l1, l3) == true;


fixpoint bool wasDecrypted<t>(trace<EventParams> tr, Term msg, Term sk, int skOwner){
    return isMsg(tr, msg, Readers(cons(skOwner, nil)), pkePred) && 
    isPrivateDecKey(tr, skOwner, sk) ? isPublishable(tr, msg, pkePred ) 
    || pkePred(tr,  msg, createPk(sk)) : true;
}

lemma void DecryptSatisfiesInvariant<t>(trace<EventParams> tr, Term msg, Term sk, int skOwner);
requires canDecrypt(tr,  encrypt( createPk(sk), msg), sk, skOwner) == true;
ensures wasDecrypted(tr, msg, sk, skOwner) == true;


lemma void flowsToPublicCanFlow(trace<EventParams> tr, Label l1, Label l2);
requires  canFlow(tr, l1, Public) == true;
ensures  canFlow(tr, l1, l2) == true;

lemma void publishableImpliesCorruption(trace<EventParams> t,  Term term, Label l, list<int> ids)
requires isPublishable(t, term, pkePred) == true &*& l == Readers(ids) &*& canFlow(t, l, getLabel(term)) == true;
ensures containsCorruptId(getCorruptIds(t), ids) == true;
{
  Label TermL = getLabel(term);
  list<int> corruptIds = getCorruptIds(t);
  assert canFlow(t, TermL, Public) == true;
  flowsToPublicCanFlow(t, TermL, l);
  canFlowTransitive(t, l, TermL, Public);


}
lemma void ciphertextIsPublishable(trace<EventParams> t,  Term msg, int to, int from, Term pk);
requires canEncrypt(t, msg, to, from, pk) || (isPublishable(t, msg, pkePred) && isPublishable(t, pk, pkePred));
ensures  isPublishable(t, encrypt(pk, msg), pkePred) == true;
@*/
#endif