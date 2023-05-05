#ifndef DEFINITIONS
#define DEFINITIONS
#include "term_definition.h"
//@ #include "ghost_cells.gh"
//@ #include <listex.gh>
//@ #include <list.gh>
//@ #include "strong_ghost_lists.gh"
//@ #include "quantifiers.gh"
#define Trace trace<EventParams>

// Clients can instantiate this library by doing the following steps:
// 1) provide a body for the following functions by defining the corresponding
//    macros and set macro `PROTOCOL_SPECIFIC_VERIFICATION`
// 2) Write an implementation of the lemmas in `protocol_specific_lemmas.h` and
//    prove the corresponding c file

// Macros
// - UNIQUE
//    body for the fixpoint `bool isUnique(int type)` that should return true for
//    unique events
// - CONSISTENCY
//    body for the fixpoint `bool eventConsistency(EventParams t, int type)` that should
//    return true if an event's parameters satisfy some protocol-specific properties
// - PKEPRED
//    body for the fixpoint `bool pkePred(trace<EventParams> tr, Term plaintext, Term pk)`
//    that specific properties for plaintexts
// - UNIQUE_WITNESS
//    body for the fixpoint `Term eventUniquenessWitness<t>(EventADT<t> e)` that returns
//    the term acting as the uniqueness witness for event `e`
// - EVENT_PRED
//    body for the fixpoint `bool event_pure_pred(EventADT<EventParams> e, int principal, trace<EventParams> tr)`
//    that should return true if a protocol-specific event satisfies protocol-specific properties
// - EVENT_PARAMS
//    constructors for the EventParams ADT

/*
this multi-line comment illustrates how protocol-specific bodies can be provided via the macros

#define PROTOCOL_SPECIFIC_VERIFICATION

// bool isUnique(int type) UNIQUE
#define UNIQUE { // your code goes here }

// bool eventConsistency(EventParams t, int type) CONSISTENCY
#define CONSISTENCY { // your code goes here}

// bool pkePred(trace<EventParams> tr, Term plaintext, Term pk) PKEPRED
#define PKEPRED  { // Your code goes here}

Term eventUniquenessWitness<t>(EventADT<t> e) UNIQUE_WITNESS
#define UNIQUE_WITNESS { // Your Code Goes here}

//bool event_pure_pred(EventADT<EventParams> e, int principal, trace<EventParams> tr) EVENT_PRED
#define EVENT_PRED {Your code goes here}

// provide protocol-specific constructors for the event ADT
// inductive EventParams = EVENT_PARAMS
#define EVENT_PARAMS  | Dummy; 
*/


#ifndef PROTOCOL_SPECIFIC_VERIFICATION
// these are the protocol-independent macro definitions that are used when verifying the library.
// i.e. we make no assumptions about the actual fixpoint definitions by treating them as abstract
#define UNIQUE ;
#define CONSISTENCY ;
#define PKEPRED ;
#define UNIQUE_WITNESS ;
#define EVENT_PRED ;
#define EVENT_PARAMS  | Dummy;
#endif


/*@
fixpoint bool pkePred(Trace tr, Term plaintext, Term pk) PKEPRED

inductive EventParams = EVENT_PARAMS
inductive EventADT<t> = newEvent(int type, t params);


/*--- Trace Definition ----*/
inductive trace<EventParams> = 
 | root(list<Term> publicTerms)
 | makeEvent(trace<EventParams>, int principal, EventADT<EventParams> e) 
 | makeCorrupt(trace<EventParams>, int principal) 
 | makeMessage(trace<EventParams>, int to, int from, Term)
 | makeDropMessage(trace<EventParams>, int to, int from,  Term)
 | makeNonce(trace<EventParams>, Term bytes, Label)
 | makePublic(trace<EventParams>, Term);
@*/
#endif
