#include "ghost_trace.h"
/*@
lemma void snapshot_suffix_hold_event(trace<EventParams> global_trace, list<int> snaps) 
requires snapshot_suffix_forall(snaps, ?t) &*& global_trace == makeEvent(t, _,_);
ensures snapshot_suffix_forall(snaps, global_trace);
{

  switch(snaps)
  {    
    case nil: open snapshot_suffix_forall(snaps, t); 
              close snapshot_suffix_forall(snaps, global_trace);
    case cons(x, xs) : 
     open snapshot_suffix_forall(snaps, t);
     snapshot_suffix_hold_event(global_trace, xs);
     close snapshot_suffix_forall(snaps, global_trace);
   }
}

lemma void snapshot_suffix_hold_message(trace<EventParams> global_trace, list<int> snaps) 
requires snapshot_suffix_forall(snaps, ?t) &*& global_trace == makeMessage(t, _,_,_);
ensures snapshot_suffix_forall(snaps, global_trace);
{

  switch(snaps)
  {    
    case nil: open snapshot_suffix_forall(snaps, t); 
              close snapshot_suffix_forall(snaps,global_trace);
    case cons(x, xs) : 
     open snapshot_suffix_forall(snaps, t);
     snapshot_suffix_hold_message(global_trace, xs);
     close snapshot_suffix_forall(snaps, global_trace);
   }
}


lemma void snapshot_reflexive<t>(trace<EventParams> t1)
requires true;
ensures  individual_snapshot_suffix(t1, t1) == true;
{
      switch(t1){
      case root(root_terms) :  
      case makeEvent(t0, pr, e): 
      case makeCorrupt(t0, id) : 
      case makeMessage(t0,to,from,term) : 
      case makeDropMessage(t0, to, from, term) : 
      case makeNonce(t0, term, l)  : 
      case makePublic(t0, term) : 
        
    }
}

lemma void snapshot_transitive<t>(trace<EventParams> t1, trace<EventParams> t2, trace<EventParams> t3)
requires individual_snapshot_suffix(t1, t2) && individual_snapshot_suffix(t2, t3);
ensures  individual_snapshot_suffix(t1, t3) == true;
{
      switch (t3){
            	case root(root_terms) :  
      	     	case makeEvent(t0, pr, e): t2 != t3 ? snapshot_transitive(t1, t2,  t0) : true;
      	     	case makeCorrupt(t0, id) :t2 != t3 ? snapshot_transitive(t1, t2,  t0) : true;
      		case makeMessage(t0,to,from,term) : t2 != t3 ? snapshot_transitive(t1, t2,  t0) : true;
      		case makeDropMessage(t0, to, from, term) : t2 != t3 ? snapshot_transitive(t1, t2,  t0) : true;
      	        case makeNonce(t0, term, l)  : t2 != t3 ? snapshot_transitive(t1, t2,  t0) : true;
      		case makePublic(t0, term) : t2 != t3 ? snapshot_transitive(t1, t2,  t0) : true;
      }
}

lemma void snapshot_suffix_hold_nonce<t>(trace<EventParams> global_trace, list<int> snaps) 
requires snapshot_suffix_forall(snaps, ?t) &*& global_trace == makeNonce(t, _,_);
ensures snapshot_suffix_forall(snaps, global_trace);
{

  switch(snaps)
  {    
    case nil: open snapshot_suffix_forall(snaps, t); 
              close snapshot_suffix_forall(snaps, global_trace);
    case cons(x, xs) : 
     open snapshot_suffix_forall(snaps, t);
     snapshot_suffix_hold_nonce(global_trace, xs);
     close snapshot_suffix_forall(snaps, global_trace);
   }
}

lemma void snapshot_suffix_hold_adding_message<t>(trace<EventParams> t1, trace<EventParams> bigger) 
requires bigger == makeMessage(t1, _,_,_);
ensures individual_snapshot_suffix(t1, bigger) == true;
{
  switch (bigger) {
      case root(root_terms) :   
      case makeEvent(t0, pr, e): 
      case makeCorrupt(t0, id) : 
      case makeMessage(t0,to,from,term) : snapshot_reflexive(t1);
      case makeDropMessage(t0, to, from, term) : 
      case makeNonce(t0, term, l)  : 
      case makePublic(t0, term) : 
     }

}



@*/