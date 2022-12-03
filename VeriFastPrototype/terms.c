#include "terms.h"
/*@


lemma void eventOccursMonotonic(trace<EventParams> t1,trace<EventParams> t2, int principal, EventADT<EventParams> e)
requires individual_snapshot_suffix(t1, t2) == true &*& eventOccurs(t1, principal, e) == true;
ensures eventOccurs(t2, principal, e) == true;
{
   switch(t2){
        case root(root_terms) : 
        case makeEvent(t0, p, eCurr): if(t2 != t1){
                                           eventOccursMonotonic(t1, t0,  principal,e);
                                         } 
        case makeCorrupt(t0, id) : if(t2 != t1){
                                           eventOccursMonotonic(t1, t0,  principal,e);
                                         } 
        case makeMessage(t0,to,from,term) :  if(t2 != t1){
                                           eventOccursMonotonic(t1, t0,  principal,e);
                                         } 
        case makeDropMessage(t0, to, from, term) :  if(t2 != t1){
                                           eventOccursMonotonic(t1, t0,  principal,e);
                                         } 
        case makeNonce(t0, term, l)  :  if(t2 != t1){
                                           eventOccursMonotonic(t1, t0,  principal,e);
                                         } 
        case makePublic(t0, term) :   if(t2 != t1){
                                           eventOccursMonotonic(t1, t0,  principal,e);
                                         } 
   }
}

lemma void nonceOccursMonotonic<t>(trace<EventParams> t1, trace<EventParams> t2, Term t, Label l)
requires individual_snapshot_suffix(t1, t2) == true && nonceOccurs(t1, t, l) == true;
ensures nonceOccurs(t2, t, l) == true;
{
     switch (t2) {
      case root(root_terms) :   false; 
      case makeEvent(t0, pr, e):  if(t1 != t2)  nonceOccursMonotonic(t1, t0, t,  l);
      case makeCorrupt(t0, id) :  if(t1 != t2)  nonceOccursMonotonic(t1, t0, t,  l);
      case makeMessage(t0,to,from,term):if(t1 != t2)  nonceOccursMonotonic(t1, t0, t,  l);
      case makeDropMessage(t0, to, from, term) :if(t1 != t2)  nonceOccursMonotonic(t1, t0, t,  l);
      case makeNonce(t0, term, la):  if(t == term && la == l){} else{ if( t1 != t2) nonceOccursMonotonic(t1, t0, t,  l);}
      case makePublic(t0, term) :   if(t1 != t2)  nonceOccursMonotonic(t1, t0, t,  l);
     }
}


// t2 is the larger one)
lemma void getCorruptIdsMonotonic(trace<EventParams> t1, trace<EventParams> t2)
requires individual_snapshot_suffix(t1, t2) == true;
ensures subset(getCorruptIds(t1), getCorruptIds(t2)) == true;

{          switch (t2) {
        case root(root_terms) : containsIds(getCorruptIds(t2), getCorruptIds(t1));
        case makeEvent(t0, p, e): if(t1 != t2)
                                        { 
                                         getCorruptIdsMonotonic(t1, t0); 
                                                 subset_refl(getCorruptIds(t2));
                                                 subset_trans(getCorruptIds(t1),getCorruptIds(t0),getCorruptIds(t2) );

                                                }
        
                                else containsIds(getCorruptIds(t2), getCorruptIds(t1));
        case makeCorrupt(t0, id) : if(t1 != t2)
        { 
                                         getCorruptIdsMonotonic(t1, t0); 
                                                 subset_refl(getCorruptIds(t2));
                                                 subset_trans(getCorruptIds(t1),getCorruptIds(t0),getCorruptIds(t2) );

                                                }
        
                                else containsIds(getCorruptIds(t2), getCorruptIds(t1));
        case makeMessage(t0,to,from,term) :   if(t1 != t2)
        { 
                                         getCorruptIdsMonotonic(t1, t0); 
                                         assert (subset(getCorruptIds(t1), getCorruptIds(t0)) == true);
                                                 assert getCorruptIds(t2) == getCorruptIds(t0);
                                                 subset_refl(getCorruptIds(t2));
                                                 subset_trans(getCorruptIds(t1),getCorruptIds(t0),getCorruptIds(t2) );

                                                }
        
                                else containsIds(getCorruptIds(t2), getCorruptIds(t1));
        case makeDropMessage(t0, to, from, term) :  if(t1 != t2)
        { 
                                         getCorruptIdsMonotonic(t1, t0); 
                                         assert (subset(getCorruptIds(t1), getCorruptIds(t0)) == true);
                                                 assert getCorruptIds(t2) == getCorruptIds(t0);
                                                 subset_refl(getCorruptIds(t2));
                                                 subset_trans(getCorruptIds(t1),getCorruptIds(t0),getCorruptIds(t2) );

                                                }
        
                                else containsIds(getCorruptIds(t2), getCorruptIds(t1));
        case makeNonce(t0, term, l)  :  if(t1 != t2)
        { 
                                         getCorruptIdsMonotonic(t1, t0); 
                                         assert (subset(getCorruptIds(t1), getCorruptIds(t0)) == true);
                                                 assert getCorruptIds(t2) == getCorruptIds(t0);
                                                 subset_refl(getCorruptIds(t2));
                                                 subset_trans(getCorruptIds(t1),getCorruptIds(t0),getCorruptIds(t2) );

                                                }
        
                                else containsIds(getCorruptIds(t2), getCorruptIds(t1));
        case makePublic(t0, term) : if(t1 != t2)
        { 
                                         getCorruptIdsMonotonic(t1, t0); 
                                         assert (subset(getCorruptIds(t1), getCorruptIds(t0)) == true);
                                                 assert getCorruptIds(t2) == getCorruptIds(t0);
                                                 subset_refl(getCorruptIds(t2));
                                                 subset_trans(getCorruptIds(t1),getCorruptIds(t0),getCorruptIds(t2) );

                                                }
        
                                else containsIds(getCorruptIds(t2), getCorruptIds(t1));
    }
}

lemma void canFlowInternalReflexive(Label l1, list<int>corruptIds)
requires true;
ensures canFlowInternal(l1, l1, corruptIds) == true;
{
   switch(l1){
   case Public : canFlowInternal(l1, l1, corruptIds);
   case Readers(l1_readers):   switch (l1){
  				case Public :  false;
  				case Readers(l2_readers):  canFlowInternal(l1, l1, corruptIds);
  };
   }
  
}




lemma void canFlowReflexive<t>(Label l1, trace<EventParams> t)
requires true;
ensures canFlow(t, l1, l1) == true;
{
  canFlowInternalReflexive(l1,getCorruptIds(t));
}



lemma void canFlowInternalMonotonic<t>(trace<EventParams> t1, trace<EventParams> t2, Label l1, Label l2)
requires individual_snapshot_suffix(t1, t2) == true && canFlow(t1, l1, l2) == true;
ensures canFlow(t2, l1, l2) == true;
{
   switch(l1){
            case Public : canFlow(t2, l1, l2);
            case Readers(l1_readers):   switch (l2){
  				        case Public :   getCorruptIdsMonotonic(t1, t2);
  				                subset_intersection(getCorruptIds(t1), getCorruptIds(t2));                                               
                                                subset_intersection_helper(getCorruptIds(t1), getCorruptIds(t2), l1_readers);
                                               

  				        case Readers(l2_readers): 
  				             getCorruptIdsMonotonic(t1, t2); 
  			                    if(containsIds(l1_readers, l2_readers)){
  			                     }else{
  			                       getCorruptIdsMonotonic(t1, t2);
                                               subset_intersection(getCorruptIds(t1), getCorruptIds(t2));
                                               subset_intersection_helper(getCorruptIds(t1), getCorruptIds(t2), l1_readers);
  
  			         }
          }
   }
}


lemma void isValidMonotonic(trace<EventParams> t1, trace<EventParams> t2, Term term, fixpoint (trace<EventParams>, Term, Term, bool) p)
requires individual_snapshot_suffix(t1, t2) == true &*& isValid(t1, term, p) == true &*& p == pkePred;
ensures isValid(t2, term, pkePred) == true;
{
   switch(term){
        case IntConstant(value): 
    	case  StringConstant(str): 
        case EncryptedTerm(pk, plaintext): if(p(t1, plaintext, pk) == true)
                                             {  
                                               pkeMonotonic(t1, t2, plaintext, pk);
                                               assert p(t2, plaintext, pk) == true;
                                             }
                                           if(canFlow(t1, getLabel(plaintext), Public) == true){
                                                  isValidMonotonic(t1, t2, plaintext, p); 
                                                  canFlowInternalMonotonic(t1, t2, getLabel(plaintext), Public); 
                                                }
               
        				
                                           isValidMonotonic(t1, t2, pk, p); 
                                           isValidMonotonic(t1, t2, plaintext, p); 
                                           canFlowInternalMonotonic(t1, t2,getLabel(plaintext), getSkLabel(pk));
                                           
          
        case Hash(ht): isValidMonotonic(t1, t2, ht, p);
    	case PublicKey(skKey) : isValidMonotonic(t1, t2, skKey, p); 
        case Nonce(nt, l):  nonceOccursMonotonic(t1, t2, term, l);
        case TwoTuple(Term1, Term2): isValidMonotonic(t1, t2, Term1, p); 
                                         isValidMonotonic(t1, t2, Term2, p); 
        case ThreeTuple(Term1, Term2, Term3): isValidMonotonic(t1, t2, Term1, p); 
                                         isValidMonotonic(t1, t2, Term2, p);
                                         isValidMonotonic(t1, t2, Term3, p);
        case FourTuple(Term1, Term2, Term3, Term4): isValidMonotonic(t1, t2, Term1, p); 
                                         	    isValidMonotonic(t1, t2, Term2, p);
                                              isValidMonotonic(t1, t2, Term4, p);
                                                    isValidMonotonic(t1, t2, Term3, p); 

   }
}

lemma void isMsgMonotonic(trace<EventParams> t1, trace<EventParams> t2, Term term, Label label, fixpoint (trace<EventParams>, Term, Term, bool) p)
requires individual_snapshot_suffix(t1, t2) == true &*& isMsg(t1, term, label, p) == true &*& p == pkePred;
ensures isMsg(t2, term, label, p) == true ;
{

	isValidMonotonic(t1, t2, term, p);
	canFlowInternalMonotonic(t1, t2, getLabel(term), label);

}

lemma void isPublishableMonotonic<t>(trace<EventParams> t1, trace<EventParams> t2, Term term, fixpoint (trace<EventParams>, Term, Term, bool) p)
requires individual_snapshot_suffix(t1, t2) == true &*& isPublishable(t1, term, p) == true &*& p == pkePred;
ensures isPublishable(t2, term, p) == true ;
{
	isMsgMonotonic(t1, t2, term, Public, p);
}

lemma void messageInvMonotonic<t>(trace<EventParams> t1, trace<EventParams> t2, int to, int from, Term term,  fixpoint (trace<EventParams> t, Term, Term, bool)  p)
requires individual_snapshot_suffix(t1, t2) == true &*& messageInv(to, from, term,t1, p) == true &*& p == pkePred ;
ensures messageInv(to, from, term,t2, p) == true;
{
  isPublishableMonotonic(t1, t2, term, p);
}
 
 


lemma void noncePointerIsUniqueContradiction(int x, int y)
requires ghost_cell(x, _) &*& ghost_cell(y, _) &*& x == y;
ensures false;
{
  merge_fractions ghost_cell(x,_); 
  ghost_cell_fraction_info(x);
}


/* Proves a contradiction if you have 2 of the same Nonce Resources */
lemma void uniqueHelper(trace<EventParams> tr, Term t, Label l, int i)
requires valid_trace(tr) &*& nonceAt(tr, t, l, i) == true &*& ghost_cell(getCellId(t), _);
ensures false; 
{
 switch(tr){
 case root(root_terms): false;
 case makeEvent(t0, pr, e):   open valid_trace(tr);
                              uniqueHelper(t0, t, l, i);  
                              close valid_trace(tr);
 case makeCorrupt(t0, id) :   open valid_trace(tr);
                              uniqueHelper(t0, t, l,i);    
                              close valid_trace(tr);
 case makeMessage(t0,to,from,term):  
                              open valid_trace(tr);
                              uniqueHelper(t0, t, l,  i);    
                              close valid_trace(tr);
 case makeDropMessage(t0, to, from, term) :   
                              open valid_trace(tr);
                              uniqueHelper(t0, t, l, i);  
                              close valid_trace(tr);
 case makeNonce(t0, term, la): open valid_trace(tr);
                                            if(la == l && term == t && trace_length(tr) == i)
    					       {
    					          

    					          noncePointerIsUniqueContradiction(getCellId(t), getCellId(t));
    					          assert false;
                        close valid_trace(tr);        
    					       }                                
					    else{
   						     uniqueHelper(t0, t, l, i);  
 						     close valid_trace(tr); 
 					       }                                           
 case makePublic(t0, term) :  open valid_trace(tr);
                              uniqueHelper(t0, t, l, i);   
                              close valid_trace(tr);

   }
}


lemma void nonceUnique(trace<EventParams> tr, Term t, Label l, int i, int j)
requires valid_trace(tr) &*& nonceAt(tr, t, l, i) == true &*& nonceAt(tr, t, l, j) == true;
ensures i == j &*& valid_trace(tr); 
{

 switch(tr){
 case root(root_terms): 
 case makeEvent(t0, pr, e):   open valid_trace(tr);
                              nonceUnique(t0, t, l, i, j);  
                              close valid_trace(tr);
 case makeCorrupt(t0, id) :   open valid_trace(tr);
                              nonceUnique(t0, t, l,  i, j); 
                               close valid_trace(tr);
 case makeMessage(t0,to,from,term):  open valid_trace(tr);
                                     nonceUnique(t0, t, l, i, j);  
                                     close valid_trace(tr);
 case makeDropMessage(t0, to, from, term) :   open valid_trace(tr);
                                              nonceUnique(t0, t, l, i, j);  
                                              close valid_trace(tr);
 case makeNonce(t0, term, la):   open valid_trace(tr);
                                              if(la == l && term == t)
    					       {    if(i == j){
    					               close valid_trace(tr); 
    					             }
    					            else if(trace_length(tr) == i){
    					                uniqueHelper(t0, t, l, j);
    					            } 
    					            else if(trace_length(tr) == j){
    					               uniqueHelper(t0, t, l, i);

    					            }
    					            else{
    					             nonceUnique(t0, t, l, i, j);
 						     close valid_trace(tr); 
    					            }

    					       }                                
					    else{
   						     nonceUnique(t0, t, l, i, j);
 						     close valid_trace(tr); 
 					       }                                           
 case makePublic(t0, term) :  open valid_trace(tr); 
                              nonceUnique(t0, t, l, i, j);  
                              close valid_trace(tr);
 }

}


lemma void rootIsSuffix<t>(trace<EventParams> tr, trace<EventParams> r)
requires r == root(getPublicTerms(tr));
ensures individual_snapshot_suffix(r, tr) == true;
{
  switch (tr) {
      case root(root_terms) : 
      case makeEvent(t0, pr, e):   rootIsSuffix(t0, r);
      case makeCorrupt(t0, id) :     rootIsSuffix(t0, r);
      case makeMessage(t0,to,from,term) :    rootIsSuffix(t0, r);
      case makeDropMessage(t0, to, from, term) :    rootIsSuffix(t0, r);
      case makeNonce(t0, term, l)  :    rootIsSuffix(t0, r);
      case makePublic(t0, term) :  rootIsSuffix(t0, r);
     }
}


lemma void getPublicTermsMonotonic<t>(trace<EventParams> t1, trace<EventParams> t2)
requires individual_snapshot_suffix(t1, t2) == true;
ensures getPublicTerms(t1) == getPublicTerms(t2);
{
   switch(t2){
      case root(root_terms) : 
      case makeEvent(t0, pr, e): if(t1 != t2) getPublicTermsMonotonic(t1, t0); 
      case makeCorrupt(t0, id) : if(t1 != t2) getPublicTermsMonotonic(t1, t0); 
      case makeMessage(t0,to,from,term) :if(t1 != t2) getPublicTermsMonotonic(t1, t0); 
      case makeDropMessage(t0, to, from, term) : if(t1 != t2) getPublicTermsMonotonic(t1, t0); 
      case makeNonce(t0, term, l)  : if(t1 != t2) getPublicTermsMonotonic(t1, t0); 
      case makePublic(t0, term) : if(t1 != t2) getPublicTermsMonotonic(t1, t0); 
   }
}

lemma void msgOccursMonotonic<t>(Term t, int to, int from, trace<EventParams> tr, trace<EventParams> global_trace)
requires individual_snapshot_suffix(tr, global_trace) && msgOccurs(t, to, from, tr);
ensures msgOccurs(t, to, from, global_trace) == true;
{
     switch (global_trace) {
      case root(root_terms) : 
      case makeEvent(t0, pr, e): if(global_trace != tr)  msgOccursMonotonic(t, to, from, tr, t0);
      case makeCorrupt(t0, id) : if(global_trace != tr)  msgOccursMonotonic(t, to, from, tr, t0);
      case makeMessage(t0,to1,from1,term) :  if(t == term && to1 == to && from1 == from){}
                     else{ 
                       if(global_trace != tr) 
                         msgOccursMonotonic(t, to, from, tr, t0);
                     }
      case makeDropMessage(t0, to1, from1, term) :  if(global_trace != tr) msgOccursMonotonic(t, to, from, tr, t0);
      case makeNonce(t0, term, l)  : if(global_trace != tr) msgOccursMonotonic(t, to, from, tr, t0);
      case makePublic(t0, term) :  if(global_trace != tr) msgOccursMonotonic(t, to, from, tr, t0);
     }
 }
@*/