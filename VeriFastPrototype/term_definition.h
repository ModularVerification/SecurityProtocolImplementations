#ifndef TERM_DEFINITIONS
#define TERM_DEFINITIONS

// #include <listex.gh>
// #include <list.gh>
// #include "strong_ghost_lists.gh"
/*@
// since this is a prototypical library, we currently only support 
// Public and Readers(...) as secrecy labels
inductive Label = Public | Readers (list<int> readers);


inductive Term = | IntConstant(int value)                 
                 | StringConstant(char* str)
                 | EncryptedTerm(Term pk, Term t)
                 | Hash(Term t) 
                 | Nonce(list<char> bytes, Label l)
                 | PublicKey(Term t)
                 | TwoTuple(Term t1, Term t2)
                 | ThreeTuple(Term t1, Term  t2, Term t3)
                 | FourTuple(Term t1, Term  t2, Term t3, Term t4);
@*/
#endif
