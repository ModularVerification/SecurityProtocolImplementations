#include "event_lemmas.h" 
/*@
lemma void eventIsContradictionHelper(EventADT<EventParams> e1, EventADT<EventParams> e2, int principal1, int principal2, trace<EventParams> tr)
requires   eventOccurs(tr, principal2, e2) == true &*& 
eventUniquenessWitness((e1)) == eventUniquenessWitness((e2)) &*& isUnique(getEventType(e1)) == true
&*& getEventType(e1) == getEventType(e2) &*& valid_trace(tr) &*& event_pred(principal1, e1, ?tx);  
ensures principal1 == principal2 &*& e1 == e2 &*& valid_trace(tr);
{

 switch(tr){
       case root(rootTerms) : 
        case makeEvent(t0, p, eCurr): open valid_trace(tr);  
                                      if(principal2 == p && e2 == eCurr) 
                                      {
                                      open event_pred(principal1, e1, tx);
                                      open event_pred(principal2, e2, t0); 
                                      open EventUniqueResource(eventUniquenessWitness((e1)), getEventType(e1));
                                      assert ghost_cell(?e1_idx, _);
                                      open EventUniqueResource(eventUniquenessWitness((e2)), getEventType(e2));
                                      assert ghost_cell(?e2_idx, _);
                                      noncePointerIsUniqueContradiction(e1_idx, e2_idx);
                                      } 
                                      else  
                                      {
                                      eventIsContradictionHelper(e1, e2, principal1, principal2, t0);
                                       }
                                      close valid_trace(tr);
        case makeCorrupt(t0, id) :     open valid_trace(tr); 
                                       eventIsContradictionHelper(e1, e2, principal1, principal2, t0); 
                                       close valid_trace(tr); 
        case makeMessage(t0,to,from,term) :     open valid_trace(tr); 
                                               eventIsContradictionHelper(e1, e2, principal1, principal2, t0);
                                               close valid_trace(tr);
        case makeDropMessage(t0, to, from, term) :     open valid_trace(tr);
                                                       eventIsContradictionHelper(e1, e2, principal1, principal2, t0); 
                                                       close valid_trace(tr);
        case makeNonce(t0, term, l)  :     open valid_trace(tr);
                                           eventIsContradictionHelper(e1, e2, principal1, principal2, t0); 
                                           close valid_trace(tr);
        case makePublic(t0, term) :     open valid_trace(tr);
                                        eventIsContradictionHelper(e1, e2, principal1, principal2, t0); 
                                        close valid_trace(tr);
   
   }

}


lemma void eventOnTraceImpliesEventPred(EventADT<EventParams> e1, EventADT<EventParams> e2, int principal1, int principal2, trace<EventParams> tr)
requires eventOccurs(tr, principal1, e1) == true &*& eventOccurs(tr, principal2, e2) == true &*& 
eventUniquenessWitness((e1)) == eventUniquenessWitness((e2)) &*& isUnique(getEventType(e1)) == true
&*& getEventType(e1) == getEventType(e2) &*& valid_trace(tr); 
ensures principal1 == principal2 &*& e1 == e2 &*& valid_trace(tr);
{

    switch(tr){
        case root(rootTerms) : 
        case makeEvent(t0, p, eCurr): open valid_trace(tr);  
                           if(e1 == e2 && principal1 == principal2)
                            { 
                             close valid_trace(tr);
                             return;
                            }
                           else if (principal1 == p && e1 == eCurr) {
                                 eventIsContradictionHelper(e1, e2, principal1, principal2, t0);
                            } 
                            else if(principal2 == p && e2 == eCurr) {
                                eventIsContradictionHelper(e2, e1, principal2, principal1, t0);
                            } 
                        
                           else  eventOnTraceImpliesEventPred(e1, e2, principal1, principal2, t0);
                           close valid_trace(tr);
        case makeCorrupt(t0, id) :     open valid_trace(tr); eventOnTraceImpliesEventPred(e1, e2, principal1, principal2, t0); close valid_trace(tr); 
        case makeMessage(t0,to,from,term) :     open valid_trace(tr); eventOnTraceImpliesEventPred(e1, e2, principal1, principal2, t0);close valid_trace(tr);
        case makeDropMessage(t0, to, from, term) :     open valid_trace(tr);eventOnTraceImpliesEventPred(e1, e2, principal1, principal2, t0); close valid_trace(tr);
        case makeNonce(t0, term, l)  :     open valid_trace(tr);eventOnTraceImpliesEventPred(e1, e2, principal1, principal2, t0); close valid_trace(tr);
        case makePublic(t0, term) :     open valid_trace(tr);eventOnTraceImpliesEventPred(e1, e2, principal1, principal2, t0); close valid_trace(tr);
   
   }


}

lemma void UniqueEventsAreUnique(trace<EventParams> suffix, trace<EventParams> global_trace, int principal1, int principal2, EventADT<EventParams> e1, EventADT<EventParams> e2)
requires individual_snapshot_suffix(suffix, global_trace) == true &*& valid_trace(global_trace) &*& 
eventOccurs(suffix, principal1, e1) == true &*& eventOccurs(suffix, principal2, e2) == true &*& 
eventUniquenessWitness((e1)) == eventUniquenessWitness((e2)) &*& isUnique(getEventType(e1)) == true
&*& getEventType(e1) == getEventType(e2);
ensures principal1 == principal2 &*& e1 == e2 &*& valid_trace(global_trace);
{
     eventOccursMonotonic(suffix, global_trace, principal1, e1);
     eventOccursMonotonic(suffix, global_trace, principal2, e2);
     eventOnTraceImpliesEventPred(e1, e2, principal1, principal2, global_trace);
   
   
}


@*/