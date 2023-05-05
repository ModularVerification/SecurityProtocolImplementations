#include "inv_finder.h"

/*@
lemma void snapshot_implies_length(trace<EventParams> tr2, trace<EventParams> tr)
requires individual_snapshot_suffix(tr2, tr) == true;
ensures trace_length(tr2) <= trace_length(tr);
{  
    switch (tr) {
      case root(root_terms) : 
      case makeEvent(t0, pr, e):  tr != tr2 ? snapshot_implies_length(tr2, t0):  true ;
      case makeCorrupt(t0, id) :  tr != tr2 ? snapshot_implies_length(tr2, t0):  true ;
      case makeMessage(t0,to,from,term) :  tr != tr2 ? snapshot_implies_length(tr2, t0):  true ;
      case makeDropMessage(t0, to, from, term) :  tr != tr2 ? snapshot_implies_length(tr2, t0):  true ;
      case makeNonce(t0, term, l)  :  tr != tr2 ? snapshot_implies_length(tr2, t0):  true ;
      case makePublic(t0, term) :  tr != tr2 ? snapshot_implies_length(tr2, t0):  true ;
     }
}
lemma void getLengthInv(list<int> snap, trace<EventParams> global_trace, int x)
requires snapshot_suffix_forall(snap, global_trace) &*& [1/2]ghost_cell<Trace>(x, ?snapshot) &*& mem(x, snap) == true;
ensures  snapshot_suffix_forall(snap, global_trace)&*& [1/2]ghost_cell<Trace>(x, snapshot) &*& trace_length(snapshot) <= trace_length(global_trace) &*& mem(x, snap) == true;
{
    switch(snap){
      case nil: 
      case cons(y, ys): 

      if(x == y)
      {        open snapshot_suffix_forall(snap, global_trace);
         assert  [1/2]ghost_cell<Trace>(x, snapshot);
         assert [1/2]ghost_cell<Trace>(y, ?snapshot_2);
               close snapshot_suffix_forall(snap, global_trace);
      }
      else{
            open snapshot_suffix_forall(snap, global_trace);
           getLengthInv(ys, global_trace,x);
                 close snapshot_suffix_forall(snap, global_trace);
      }

    }
}

lemma int getMessageSender(trace<EventParams> tr, Term mTerm)
requires mem(mTerm, getMessagePayloads(tr, nil)) == true;
ensures  senderOccurs(tr, result) == true;
{
   switch (tr) {
      case root(root_terms) : 
      case makeEvent(t0, pr, e): return  getMessageSender(t0, mTerm);
      case makeCorrupt(t0, id) : return  getMessageSender(t0, mTerm);
      case makeMessage(t0,to,from,term) : if (mTerm == term)
                                               return from;
                                          else  { 
                                            messagePayloadsMemLemma(tr, t0, mTerm, term, to, from);   
                                            return getMessageSender(t0, mTerm);
                                          }
      case makeDropMessage(t0, to, from, term) : return getMessageSender(t0, mTerm);
      case makeNonce(t0, term, l)  : return  getMessageSender(t0, mTerm);
      case makePublic(t0, term) : return  getMessageSender(t0, mTerm);
     }
}

lemma pair<int,int> getMessageSenderReceiver(trace<EventParams> tr, Term mTerm)
requires mem(mTerm, getMessagePayloads(tr, nil)) == true;
ensures  msgOccurs(mTerm, fst(result), snd(result), tr) == true;
{
   switch (tr) {
      case root(root_terms) : 
      case makeEvent(t0, pr, e): return  getMessageSenderReceiver(t0, mTerm);
      case makeCorrupt(t0, id) : return  getMessageSenderReceiver(t0, mTerm);
      case makeMessage(t0,to,from,term) : if (mTerm == term)
                  return pair(to, from);
                  else{ 
                                          messagePayloadsMemLemma(tr, t0, mTerm, term, to, from);   
                                          return getMessageSenderReceiver(t0, mTerm);
                                          }
      case makeDropMessage(t0, to, from, term) : return getMessageSenderReceiver(t0, mTerm);
      case makeNonce(t0, term, l)  : return  getMessageSenderReceiver(t0, mTerm);
      case makePublic(t0, term) : return  getMessageSenderReceiver(t0, mTerm);
     }
}


lemma int getMessageReceiver(trace<EventParams> tr, Term mTerm)
requires mem(mTerm, getMessagePayloads(tr, nil)) == true;
ensures  receiverOccurs(tr, result) == true;
{
   switch (tr) {
      case root(root_terms) : 
      case makeEvent(t0, pr, e): return  getMessageReceiver(t0, mTerm);
      case makeCorrupt(t0, id) : return  getMessageReceiver(t0, mTerm);
      case makeMessage(t0,to,from,term) : if (mTerm == term)
                  return to;
                  else{ 
                                          messagePayloadsMemLemma(tr, t0, mTerm, term, to, from);   
                                          return getMessageReceiver(t0, mTerm);
                                          }
      case makeDropMessage(t0, to, from, term) : return getMessageReceiver(t0, mTerm);
      case makeNonce(t0, term, l)  : return  getMessageReceiver(t0, mTerm);
      case makePublic(t0, term) : return  getMessageReceiver(t0, mTerm);
     }
}






/*------------ Extract Public Invariants --------------*/
lemma void getPublicInv(trace<EventParams> global_trace, trace<EventParams> snapshot)
requires valid_trace(global_trace) &*& individual_snapshot_suffix(snapshot, global_trace) == true;
ensures valid_trace(global_trace) &*& PublicInv(getPublicTerms(snapshot), root(getPublicTerms(snapshot))) == true;
{

   switch (global_trace) {
      case root(root_terms) : open valid_trace(global_trace); 
                              close valid_trace(global_trace); 
      //assert PublicInv(getPublicTerms(global_trace, root(getPublicTerms(global_trace))) == true;
      case makeEvent(t0, pr, e): open valid_trace(global_trace); 
      if(global_trace != snapshot) getPublicInv(t0, snapshot); 
      else{ snapshot_reflexive(t0); getPublicInv(t0, t0); }
      close valid_trace(global_trace);
      
      case makeCorrupt(t0, id) : open valid_trace(global_trace); 
      if(global_trace != snapshot) getPublicInv(t0, snapshot); 
      else{ snapshot_reflexive(t0); getPublicInv(t0, t0); }
      close valid_trace(global_trace);
      
      case makeMessage(t0,to,from,term) : open valid_trace(global_trace); 
      if(global_trace != snapshot) getPublicInv(t0, snapshot); 
      else{ snapshot_reflexive(t0); getPublicInv(t0, t0); }
      close valid_trace(global_trace);
      
      case makeDropMessage(t0, to, from, term) : 
      open valid_trace(global_trace); 
      if(global_trace != snapshot) 
         getPublicInv(t0, snapshot); 
      else{ snapshot_reflexive(t0); getPublicInv(t0, t0); }
      close valid_trace(global_trace);
      
      case makeNonce(t0, term, l)  : open valid_trace(global_trace); if(global_trace != snapshot) getPublicInv(t0, snapshot); 
      else{ snapshot_reflexive(t0); getPublicInv(t0, t0); }close valid_trace(global_trace);
      
      case makePublic(t0, term) :open valid_trace(global_trace); if(global_trace != snapshot) getPublicInv(t0, snapshot); 
      else{ snapshot_reflexive(t0); getPublicInv(t0, t0); }close valid_trace(global_trace);
      
     }
}


lemma void getPublicInvWrapper(trace<EventParams> global_trace, list<int> snap, int x)
requires [1/2]ghost_cell<Trace>(x, ?snapshot)  &*& 
  mem(x, snap) == true &*& distinct(snap) == true   &*&  
  ghost_cell<Trace>(?id, global_trace) &*& valid_trace(global_trace)
  &*&   snapshot_suffix_forall(snap,global_trace);
ensures [1/2]ghost_cell<Trace>(x, snapshot)  &*& 
  mem(x, snap) == true &*& distinct(snap) == true   &*&  ghost_cell<Trace>(id, global_trace) &*& valid_trace(global_trace)
  &*&   snapshot_suffix_forall(snap,global_trace) 
  &*& PublicInv(getPublicTerms(snapshot), root(getPublicTerms(snapshot))) == true
  &*& trace_length(snapshot) <= trace_length(global_trace); 
{

 
  switch(snap){
    case nil:     
         open snapshot_suffix_forall(snap, global_trace);
         close snapshot_suffix_forall(snap,  global_trace);

    case cons(l, ls): 
         open snapshot_suffix_forall(snap,  global_trace);
      if(x == l){
         merge_fractions ghost_cell(x, _); 
         getPublicInv(global_trace, snapshot);
         split_fraction ghost_cell(x, snapshot) by 1/2;
         close snapshot_suffix_forall(snap, global_trace);
         getLengthInv(snap, global_trace, x);
      }
      else {
          
             getPublicInvWrapper(global_trace, ls, x);
             close snapshot_suffix_forall(snap,  global_trace);
             getLengthInv(snap, global_trace, x);
      }
  }

}

/*------- Extract Message Invariant ---------*/
lemma trace<EventParams> getMsgInv(trace<EventParams> global_trace, trace<EventParams> snapshot, int to, int from, Term t)
requires valid_trace(global_trace) &*& individual_snapshot_suffix(snapshot, global_trace) == true 
&*& msgOccurs(t, to, from, snapshot) == true;
ensures valid_trace(global_trace) &*& isPublishable(result, t, pkePred) == true
        &*& individual_snapshot_suffix(result, snapshot) == true;
{

   switch (global_trace) {
      case root(root_terms) : 

      case makeEvent(t0, pr, e):  open valid_trace(global_trace); 
                                 if(global_trace != snapshot) 
                                       { trace<EventParams> ret  = getMsgInv(t0, snapshot, to, from, t); 
                                        close valid_trace(global_trace);
                return ret;}
             else{ 
                snapshot_reflexive(t0); 
                trace<EventParams> ret =  getMsgInv(t0, t0, to, from, t); 
                close valid_trace(global_trace);
                return ret;
               }

      
      case makeCorrupt(t0, id) : open valid_trace(global_trace); 
                                 if(global_trace != snapshot) {
                                          trace<EventParams> ret  = getMsgInv(t0, snapshot, to, from, t); 
                                        close valid_trace(global_trace);
                return ret; 
              }
             else{ 
                snapshot_reflexive(t0); 

                trace<EventParams> ret =  getMsgInv(t0, t0, to, from, t); 
                close valid_trace(global_trace);
                return ret;
               }

      
      case makeMessage(t0,to1,from1,term) : open valid_trace(global_trace); 
                                          if(global_trace != snapshot) {
                                            
                                            trace<EventParams> ret =  getMsgInv(t0, snapshot, to, from, t); 
                                                  close valid_trace(global_trace);
                                                  return ret;
                                            }
                                          else{ 
                                          if(to1 == to && from1 == from && term == t){
                                          
                                              snapshot_reflexive(t0); 
                                              close valid_trace(global_trace);
                                              return   t0;
                                              
                                           }
                                             snapshot_reflexive(t0); 
                                             trace<EventParams> ret =  getMsgInv(t0, t0, to, from, t); 
                     close valid_trace(global_trace);
                     return ret; 
                                          }

      
      case makeDropMessage(t0, to1, from1, term) : 

                                 open valid_trace(global_trace); 
                                 if(global_trace != snapshot) {
                                          trace<EventParams> ret  = getMsgInv(t0, snapshot, to, from, t); 
                                        close valid_trace(global_trace);
                return ret; 
              }
             else{ 
                snapshot_reflexive(t0); 

                trace<EventParams> ret =  getMsgInv(t0, t0, to, from, t); 
                close valid_trace(global_trace);
                return ret;
               }

      case makeNonce(t0, term, l)  :  open valid_trace(global_trace); 

                                 if(global_trace != snapshot) {
                                          trace<EventParams> ret  = getMsgInv(t0, snapshot, to, from, t); 
                                        close valid_trace(global_trace);
                return ret; 
              }
             else{ 
                snapshot_reflexive(t0); 

                trace<EventParams> ret =  getMsgInv(t0, t0, to, from, t); 
                close valid_trace(global_trace);
                return ret;
               }

      
      case makePublic(t0, term) : open valid_trace(global_trace); 
                                 if(global_trace != snapshot) {
                                          trace<EventParams> ret  = getMsgInv(t0, snapshot, to, from, t); 
                                        close valid_trace(global_trace);
                return ret; 
              } 
             else{ 
                snapshot_reflexive(t0); 

                trace<EventParams> ret =  getMsgInv(t0, t0, to, from, t); 
                close valid_trace(global_trace);
                return ret;
               }

      
     }
}



lemma trace<EventParams> getMsgInvWrapper(trace<EventParams> global_trace, list<int> snap, trace<EventParams> given_snap, int x, Term term, int to, int from)
requires [1/2]ghost_cell<Trace>(x, ?snapshot)  &*& 
  mem(x, snap) == true &*& distinct(snap) == true   &*&  
  ghost_cell<Trace>(?id, global_trace) &*& valid_trace(global_trace)
  &*&   snapshot_suffix_forall(snap,global_trace) &*&   msgOccurs(term, to, from, given_snap) == true
  &*&  individual_snapshot_suffix(given_snap, snapshot) == true;
ensures [1/2]ghost_cell<Trace>(x, snapshot)  &*& 
  mem(x, snap) == true &*& distinct(snap) == true   &*&  ghost_cell<Trace>(id, global_trace) &*& valid_trace(global_trace)
  &*&   snapshot_suffix_forall(snap,global_trace) &*& isPublishable(result, term, pkePred) == true
  &*& individual_snapshot_suffix(result, given_snap) == true  &*& trace_length(result) <= trace_length(global_trace); 
{

 
  switch(snap){
    case nil:     
         open snapshot_suffix_forall(snap, global_trace);
         close snapshot_suffix_forall(snap,  global_trace);

    case cons(l, ls): 
         open snapshot_suffix_forall(snap,  global_trace);
      if(x == l)
      {
       merge_fractions ghost_cell(x, _); 
                         snapshot_transitive(given_snap, snapshot, global_trace);
                         trace<EventParams> ret = getMsgInv(global_trace, given_snap, to, from, term);
                         split_fraction ghost_cell(x, snapshot) by 1/2;
                         close snapshot_suffix_forall(snap, global_trace);
                         getLengthInv(snap, global_trace, x);
                         snapshot_transitive(ret, given_snap, global_trace);
                         snapshot_implies_length(ret, global_trace);
                         return ret;
                }
                else 
                 {
               
               trace<EventParams> ret = getMsgInvWrapper(global_trace, ls, given_snap, x, term, to, from);
               close snapshot_suffix_forall(snap,  global_trace);

               return ret;
               
                }
  }

}

/*------- Extract Public Invariant ---------*/
lemma trace<EventParams> getPublicTermsInv(trace<EventParams> global_trace, trace<EventParams> snapshot, Term t)
requires valid_trace(global_trace) &*& individual_snapshot_suffix(snapshot, global_trace) == true 
&*& termOccursPublic(t, snapshot) == true;

ensures valid_trace(global_trace) &*& isPublishable(result, t, pkePred) == true
        &*& individual_snapshot_suffix(result, snapshot) == true;
{

   switch (global_trace) {
      case root(root_terms) : 

      case makeEvent(t0, pr, e):  open valid_trace(global_trace); 
                                 if(global_trace != snapshot)  { 
                                        trace<EventParams> ret  =  getPublicTermsInv(t0, snapshot, t); 
                                        close valid_trace(global_trace);
                                        return ret;
                                  }
             else{ 
                snapshot_reflexive(t0); 
                trace<EventParams> ret =  getPublicTermsInv(t0, t0, t); 
                close valid_trace(global_trace);
                return ret;
               }

      
      case makeCorrupt(t0, id) : open valid_trace(global_trace); 
                                 if(global_trace != snapshot) {
                                        trace<EventParams> ret  = getPublicTermsInv(t0, snapshot, t); 
                                        close valid_trace(global_trace);
                                        return ret; 
                                  }
             else{ 
                snapshot_reflexive(t0); 
                trace<EventParams> ret =  getPublicTermsInv(t0, t0, t); 
                close valid_trace(global_trace);
                return ret;
               }

      
      case makeMessage(t0,to1,from1,term) : open valid_trace(global_trace); 
                                 if(global_trace != snapshot) {
                                          trace<EventParams> ret  = getPublicTermsInv(t0, snapshot, t); 
                                          close valid_trace(global_trace);
                                           return ret; 
                                  }
             else{ 
                snapshot_reflexive(t0); 

                trace<EventParams> ret =  getPublicTermsInv(t0, t0, t); 
                close valid_trace(global_trace);
                return ret;
               }

      
      case makeDropMessage(t0, to1, from1, term) : 

                                 open valid_trace(global_trace); 
                                 if(global_trace != snapshot) {
                                          trace<EventParams> ret  = getPublicTermsInv(t0, snapshot, t); 
                                          close valid_trace(global_trace);
                                          return ret; 
                                        }
             else{ 
                snapshot_reflexive(t0); 

                trace<EventParams> ret =  getPublicTermsInv(t0, t0, t); 
                close valid_trace(global_trace);
                return ret;
               }

      case makeNonce(t0, term, l)  :  open valid_trace(global_trace); 
                                 if(global_trace != snapshot) {
                                          trace<EventParams> ret  = getPublicTermsInv(t0, snapshot, t); 
                                          close valid_trace(global_trace);
                                          return ret; 
                                  } 
             else{ 
                snapshot_reflexive(t0); 

                trace<EventParams> ret =  getPublicTermsInv(t0, t0,  t); 
                close valid_trace(global_trace);
                return ret;
               }

      
      case makePublic(t0, term) : open valid_trace(global_trace); 
                                 if(global_trace != snapshot) {
                                        trace<EventParams> ret  = getPublicTermsInv(t0, snapshot,  t); 
                                        close valid_trace(global_trace);
                                        return ret; 
                                  } 
             else{ 
             if(term == t){
                        snapshot_reflexive(t0); 
                                            close valid_trace(global_trace); 
                                            return t0;
                                        }
                snapshot_reflexive(t0); 
                trace<EventParams> ret =  getPublicTermsInv(t0, t0, t); 
                close valid_trace(global_trace);
                return ret;
               }

      
     }
}



lemma trace<EventParams> getPublicTermsWrapper(trace<EventParams> global_trace, list<int> snap, trace<EventParams> given_snap, int x, Term term)
requires [1/2]ghost_cell<Trace>(x, ?snapshot)  &*& 
  mem(x, snap) == true &*& distinct(snap) == true   &*&  
  ghost_cell<Trace>(?id, global_trace) &*& valid_trace(global_trace)
  &*&   snapshot_suffix_forall(snap,global_trace) &*&   termOccursPublic(term, given_snap) == true
  &*&  individual_snapshot_suffix(given_snap, snapshot) == true;
ensures [1/2]ghost_cell<Trace>(x, snapshot)  &*& 
  mem(x, snap) == true &*& distinct(snap) == true   &*&  ghost_cell<Trace>(id, global_trace) &*& valid_trace(global_trace)
  &*&   snapshot_suffix_forall(snap,global_trace) &*& isPublishable(result, term, pkePred) == true
  &*& individual_snapshot_suffix(result, given_snap) == true
  &*& termOccursPublic(term, given_snap) == true
  &*& trace_length(result) <= trace_length(global_trace); 
{

 
  switch(snap){
    case nil:     
         open snapshot_suffix_forall(snap, global_trace);
         close snapshot_suffix_forall(snap,  global_trace);

    case cons(l, ls): 
         open snapshot_suffix_forall(snap,  global_trace);
      if(x == l)
      {
       merge_fractions ghost_cell(x, _); 
                         snapshot_transitive(given_snap, snapshot, global_trace);
                         trace<EventParams> ret = getPublicTermsInv(global_trace, given_snap, term);
                         split_fraction ghost_cell(x, snapshot) by 1/2;
                         close snapshot_suffix_forall(snap, global_trace);
                        snapshot_transitive(ret, given_snap, global_trace);
                         snapshot_implies_length(ret, global_trace);

                         return ret;
                }
                else 
                 {
                // open snapshot_suffix_forall(snap, global_trace);
               
             trace<EventParams> ret = getPublicTermsWrapper(global_trace, ls, given_snap, x, term);
               close snapshot_suffix_forall(snap,  global_trace);
               return ret;
               
                }
  }

}

/*---------------Retrieve Public Terms Inv ------------------*/
@*/
void findEntryWithPurePublicInvWithSnap(trace<EventParams> snap, int noOfClients, struct TraceManager *tm, Term term)
/*@ requires [1/2]ghost_cell<Trace>(?x, ?snapshot) &*& TraceManagerMem(tm, noOfClients, x) &*& 
    individual_snapshot_suffix(snap, snapshot) == true &*& mem(term, getPublicTerms(snap)) == true;
    @*/
/*@  ensures [1/2]ghost_cell<Trace>(x, snapshot) &*& TraceManagerMem(tm, noOfClients, x) &*& 
     mem(term, getPublicTerms(snap)) == true
    &*& individual_snapshot_suffix(snap, snapshot) == true &*& PublicInv(getPublicTerms(snap), root(getPublicTerms(snap))) == true;
@*/
{
      //@ open TraceManagerMem(tm, noOfClients, x);
      acquire(tm->og);
      //@ open combined_ctr_locked(tm->og, noOfClients)();
      //@ assert tm->og  |-> ?og;

      //@ assert ghost_cell(?global_id, ?global_trace) &*& valid_trace(global_trace);
      //@ assert snapshot_suffix_forall(?snap_list, global_trace);
      //@ getPublicInvWrapper(global_trace, snap_list,  x);
      //@ assert PublicInv(getPublicTerms(snapshot), root(getPublicTerms(snapshot))) == true;

      //@ assert trace_length(snapshot) <= trace_length(global_trace);
      //@ close combined_ctr_release(og, og->size)();
      release(tm->og);
      //@close TraceManagerMem(tm, noOfClients, x);
      //@ getPublicTermsMonotonic(snap, snapshot);


}
trace<EventParams> PublicTermImpliesPublicInvWithSnap(struct TraceManager *tm, int noOfClients, trace<EventParams> snap, Term term)
/*@ requires  [1/2]ghost_cell<Trace>(?x, ?snapshot) &*& TraceManagerMem(tm, noOfClients, x) &*& 
    individual_snapshot_suffix(snap, snapshot) == true &*& mem(term, getPublicTerms(snap)) == true;@*/
    
/*@ ensures [1/2]ghost_cell<Trace>(x, snapshot) &*& TraceManagerMem(tm, noOfClients, x) &*&
     individual_snapshot_suffix(result, snap) == true &*& PublicInv(getPublicTerms(snap), result) == true
    &*& individual_snapshot_suffix(result, snap) == true; @*/
{
         findEntryWithPurePublicInvWithSnap(snap, noOfClients, tm, term);
         //@ rootIsSuffix(snap, root(getPublicTerms(snap)));
         return root(getPublicTerms(snap));
         
}


/*---------------Retrieve Message Terms Inv ------------------*/


void findEntryWithPureMsgInvWithSnap(trace<EventParams> snap, int noOfClients, struct TraceManager *tm, Term term)
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
{
      //@ open TraceManagerMem(tm, noOfClients, x);
      acquire(tm->og);
      //@ assert tm->og  |-> ?og;
      //@ open combined_ctr_locked(og, og->size)();
      //@ assert ghost_cell(?global_id, ?global_trace) &*& valid_trace(global_trace);

      //@ assert snapshot_suffix_forall(?snap_list, global_trace);

      //@ trace<EventParams> to_ret = getMsgInvWrapper(global_trace, snap_list, snap, x,  term,  to,  from);
      //@ int id = create_ghost_cell<Trace>(to_ret);
      // getLengthInv(snap_list, global_trace, id);
      //@ close combined_ctr_release(og, og->size)();
      release(tm->og);
      //@close TraceManagerMem(tm, noOfClients, x);



}



void PublicTermImpliesMsgInvWithSnap(struct TraceManager *tm, int noOfClients, trace<EventParams> snap, Term term)
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
{
         findEntryWithPureMsgInvWithSnap(snap, noOfClients, tm, term);
     
         
}

void madePublicTermImpliesPublishableSnap(struct TraceManager *tm, int noOfClients, trace<EventParams> snap, Term term)
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
{
      //@ open TraceManagerMem(tm, noOfClients, x);
      acquire(tm->og);
      //@ assert tm->og  |-> ?og;
            //@ open combined_ctr_locked(og, og->size)();

      //@ assert ghost_cell(?global_id, ?global_trace) &*& valid_trace(global_trace);

      //@ assert snapshot_suffix_forall(?snap_list, global_trace);

      //@ trace<EventParams> to_ret =  getPublicTermsWrapper(global_trace, snap_list, snap, x,  term);
      //@ int id = create_ghost_cell<Trace>(to_ret);
      //@ close combined_ctr_release(og, og->size)();

      release(tm->og);
      //@close TraceManagerMem(tm, noOfClients, x);
     
         
}





/*@ lemma void getPublishableFromPublicInv(Term t, list<Term> root_terms, trace<EventParams> tr)
requires PublicInv(root_terms, tr) == true &*& mem(t, root_terms) == true;
ensures isPublishable(tr, t, pkePred) == true; 
{
switch(root_terms){
 case nil: 
 case cons(x, xs):  if(t == x) {} else{ getPublishableFromPublicInv(t, xs, tr);}
}
}
@*/