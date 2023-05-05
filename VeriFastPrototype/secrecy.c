#include "secrecy.h"


void AttackerOnlyKnowsPublishableValuesWithSnap(struct TraceManager *tm, int noOfClients, trace<EventParams> snap, Term term) 
/*@requires [1/2]ghost_cell<Trace>(?x, ?snapshot) &*& TraceManagerMem(tm, noOfClients, x) &*& 
         attackerKnows(snap, term) == true &*& individual_snapshot_suffix(snap, snapshot) == true;
         @*/
/*@ ensures isPublishable(snap, term, pkePred) == true &*& [1/2]ghost_cell<Trace>(x, snapshot) &*& TraceManagerMem(tm, noOfClients, x);
@*/
{       

	list<Term> publicTerms = getPublicTerms(snap);
	list<Term> msgPayloads = getMessagePayloads(snap, nil);
	list<Term> publishedTerms = getTermsMadePublic(snap, nil);
        //@ mem_append(term, append(publishedTerms, msgPayloads), publicTerms);
        //@ mem_append(term, publishedTerms, msgPayloads);
        //@ assert mem(term, append (append(getTermsMadePublic(snap, nil), getMessagePayloads(snap, nil)), getPublicTerms(snap))) == true;
	if (mem(term, getPublicTerms(snap))) {
		trace<EventParams> prev = PublicTermImpliesPublicInvWithSnap(tm, noOfClients, snap, term);
                //@ getPublishableFromPublicInv(term, publicTerms, prev);
		//@ isPublishableMonotonic(prev, snap, term, pkePred);
		//@ assert  isPublishable(snap, term, pkePred) == true;
		 
	}  else {
                //@ assert mem(term, append(getTermsMadePublic(snap, nil), getMessagePayloads(snap, nil))) == true;
	        if (mem(term, msgPayloads)) {
	        //@pair<int,int> temp_store = getMessageSenderReceiver(snap, term);
		//@ int from  = snd(temp_store);
		//@ int to = fst(temp_store);
		//@ int id1 = create_ghost_cell(from);
		//@ int id2 = create_ghost_cell(to);
		PublicTermImpliesMsgInvWithSnap(tm, noOfClients, snap, term);
		//@ assert ghost_cell<Trace>(?cell_id, ?result);
		//@ isPublishableMonotonic(result, snap, term, pkePred);
                //@ leak ghost_cell(_, _);
                   		//@ leak ghost_cell(_,_);
                //@ leak ghost_cell<Trace>(_, _);
	}    else {
		//@ assert mem(term, publishedTerms) == true; 
		//@termOccursPublicLemma(term,snap);


		madePublicTermImpliesPublishableSnap(tm, noOfClients, snap, term);
		//@ assert ghost_cell<Trace>(?cell_id, ?result);
		//@ isPublishableMonotonic(result, snap, term, pkePred);
   		//@ leak ghost_cell(_,_);




	}
   }

}



void secrecyHelper(Term term, Trace snapshot, list<int> readers,int noOfClients,  struct TraceManager *tm)
/*@ requires  [1/2]ghost_cell<Trace>(?x, snapshot) &*& TraceManagerMem(tm, noOfClients, x) &*& 
getLabel(term) == Readers(readers) &*& length(readers) > 0 
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
{
   
       list<int> corruptedIds = getCorruptIds(snapshot);
       if(containsCorruptId(corruptedIds, readers)){
       
         switch(intersection(corruptedIds, readers)){
            case nil: 
            case cons(cID, xs): //@ assert mem(cID, intersection(corruptedIds, readers)) == true;
                              //@ mem_intersection(cID, corruptedIds, readers);
                              //@ assert Secrecy(term, snapshot, readers) == true;
                              //@ int p = create_ghost_cell(some(cID));
                                  
          } 
        
       }else{
            	//@ snapshot_reflexive(snapshot);
            	AttackerOnlyKnowsPublishableValuesWithSnap(tm, noOfClients, snapshot, term);
       
       }
}


void SecrecyLemma<t>(Term term, list<int> readers, int noOfClients,  struct TraceManager *tm, Trace snapshot)
/*@requires [1/2]ghost_cell<Trace>(?x, snapshot) &*& TraceManagerMem(tm, noOfClients, x) 
&*& isValid(snapshot, term, pkePred)   
&& length(readers) > 0 &*& (getLabel(term) == Readers(readers))
|| containsCorruptId(getCorruptIds(snapshot), readers);
@*/
/*@
ensures [1/2]ghost_cell<Trace>(x, snapshot) &*& (Secrecy(term, snapshot, readers) == true
       &*& ghost_cell<optiontype>(?id, ?result) &*& (
       switch(result){
       case some(y): return mem(y, getCorruptIds(snapshot))
       && mem(y, readers); case none: return !attackerKnows(snapshot, term) ;})
       &*& TraceManagerMem(tm, noOfClients, x));
       @*/
       

{
   if(attackerKnows(snapshot, term)){

       list<int> corruptedIds = getCorruptIds(snapshot);
       if(containsCorruptId(corruptedIds, readers)){
          switch(intersection(corruptedIds, readers)){
            case nil: 
            case cons(cID, xs): 
                              //@ assert mem(cID, intersection(corruptedIds, readers)) == true;
                              //@ mem_intersection(cID, corruptedIds, readers);

                              // assert getLabel(term) == Readers(readers) == true;
                              //@ assert containsCorruptId(getCorruptIds(snapshot), readers) == true;
                              //@ assert Secrecy(term, snapshot, readers) == true;
                              //@ int p = create_ghost_cell(some(cID));
                                  
          } 
       }
       else{
		secrecyHelper(term, snapshot, readers, noOfClients, tm );
       }
   } 
   else
     {
     //@ assert Secrecy(term, snapshot, readers) == true;
     //@ int y = create_ghost_cell(none);
    }

}
