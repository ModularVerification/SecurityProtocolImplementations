#ifndef GAMMA_H
#define GAMMA_H
#include "ghost_trace.h"
#include "terms.h"


/*---- Contains definition for the gamma function that converts terms to bytes -----*/


/*@ fixpoint list<char> createPkB(list<char> b); 

fixpoint  list<char> encryptB(list<char> plaintext, list<char>  publicKey);
fixpoint list<char> decryptB(list<char> ciphertext, list<char>  secretKey);

lemma void decryptPreservesPlaintext(list<char> plaintext, list<char> secretKey);
requires true;
ensures decryptB(encryptB(plaintext, createPkB(secretKey)),  secretKey) == plaintext;
@*/ 

/*@ fixpoint list<char> intToAbsBytes(int a); @*/

/*@ fixpoint int bytesToInt(list<char> a); @*/

/*@ fixpoint list<char> intNonceLengthB(int x); @*/


/*@ fixpoint list<char> gamma(Term t); @*/

/*@ fixpoint Term oneTerm(list<char> bytes);

lemma void oneTermInverse(list<char> bytes);
requires true;
ensures gamma(oneTerm(bytes)) == bytes;

fixpoint list<char> bytes_format_fourtuple(list<char> b1, list<char> b2, list<char> b3, list<char> b4);

lemma_auto void gammaHomomorphismForEncrypt(Term t1, Term t2);
 requires true;
 ensures (gamma(encrypt(t1, t2))) == encryptB((gamma(t1)), (gamma(t2)));
 
lemma_auto void gammaHomomorhphismForQuad(Term t1, Term t2, Term t3, Term t4);
requires true; 
 ensures gamma(FourTuple(t1, t2, t3, t4)) == bytes_format_fourtuple(gamma(t1), gamma(t2), gamma(t3), gamma(t4));

lemma_auto void gammaHomomorhphismForInt(int x);
requires true;
ensures gamma(IntConstant(x)) == intNonceLengthB(x);

lemma_auto void gammaHomomorhphismForPk(Term sk);
requires true; 
ensures gamma(createPk(sk)) == createPkB(gamma(sk));
 
 @*/
 
 #endif