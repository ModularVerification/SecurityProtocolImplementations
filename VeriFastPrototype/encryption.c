#include "encryption.h"

/*@
lemma void flowsToPublicCanFlow(trace<EventParams> tr, Label l1, Label l2)
requires  canFlow(tr, l1, Public) == true;
ensures  canFlow(tr, l1, l2) == true;
{
   switch(l1){
   case Public: 
   case Readers(l1_readers): switch(l2){
   				case Public: 
   				case Readers(l2_readers): 
   	
                           }
   }

}

lemma void canFlowTransitive(trace<EventParams> tr, Label l1, Label l2, Label l3)
requires canFlow(tr, l1, l2) == true &*& canFlow(tr, l2, l3) == true; 
ensures canFlow(tr, l1, l3) == true;
{
   switch(l1){
   case Public : canFlowInternal(l1, l2, getCorruptIds(tr));
   case Readers(l1_readers):   switch (l2){
  				case Public :  flowsToPublicCanFlow(tr, l1, l3);
  				case Readers(l2_readers): switch(l3){
  							  case Public: if (canFlow(tr, l2, Public) && canFlow(tr, l1, l2)) {
       										if(containsCorruptId( getCorruptIds(tr), l1_readers)){
       									      										    
       										}
       										else{
       										assert containsIds(l1_readers, l2_readers) == true;
       										assert subset(l2_readers, l1_readers) == true;
       										assert containsCorruptId(getCorruptIds(tr), l2_readers) == true;
       										
         									switch(intersection(getCorruptIds(tr), l2_readers)){
                 								case nil: 
                 								case cons(cID, xs):
                 								    assert mem(cID, intersection(getCorruptIds(tr), l2_readers)) == true;
                 								    mem_intersection(cID, getCorruptIds(tr), l2_readers);
                 								    mem_subset(cID, l2_readers, l1_readers);
                 								    mem_intersection(cID, getCorruptIds(tr), l1_readers);
       									            assert containsCorruptId(getCorruptIds(tr), l1_readers) == true;
       										        assert canFlow(tr, l1, l3) == true;
       										    }
       										}
    									  }
  							  case Readers(l3_readers): {
  							        if(containsCorruptId(getCorruptIds(tr),l2_readers)){
  							            if(containsCorruptId(getCorruptIds(tr), l1_readers)){
  							            
  							            }
  							            else if(containsIds(l1_readers, l2_readers)){
  							                switch(intersection(getCorruptIds(tr), l2_readers)){
                 								case nil: 
                 								case cons(cID, xs):
                 								    assert mem(cID, intersection(getCorruptIds(tr), l2_readers)) == true;
                 								    mem_intersection(cID, getCorruptIds(tr), l2_readers);
                 								    assert mem(cID, getCorruptIds(tr)) == true;
                 								    mem_subset(cID, l2_readers, l1_readers);                 							   
                 								    mem_intersection(cID, getCorruptIds(tr), l1_readers);               								    

       										}
  							            }
  							            
  							           
  							        }
  							       else if(containsIds(l2_readers, l3_readers)){
  							        
  							               if(containsCorruptId(getCorruptIds(tr), l1_readers)){
  							            
  							               }
  							               else if(containsIds(l1_readers, l2_readers)){
  							                   subset_trans(l3_readers, l2_readers, l1_readers);
                 							
  							            }
  							            
  							        }
  							     }
  				        }
  };

   }
  
}

lemma void canFlowFlowsToPublic(trace<EventParams> tr, Label l1,Label l2) 
requires canFlow(tr, l2, Public) && canFlow(tr, l1, l2);
ensures canFlow(tr, l1,Public) == true;
{
    if (canFlow(tr, l2, Public) && canFlow(tr, l1, l2)) {
       canFlowTransitive(tr, l1, l2, Public);
    }
   }

lemma void ciphertextIsPublishable(trace<EventParams> t,  Term msg, int to, int from, Term pk)
requires canEncrypt(t, msg, to, from, pk) || (isPublishable(t, msg, pkePred) && isPublishable(t, pk, pkePred));
ensures isPublishable(t, encrypt(pk, msg), pkePred) == true;
{   

    if(canEncrypt(t, msg, to, from, pk)){
         assert isValid(t, pk, pkePred) == true;
         assert isValid(t, msg, pkePred)== true;
         assert isPublishable(t, pk, pkePred) == true;
         assert canFlow(t, getLabel(encrypt(pk, msg)), Public) == true;
         assert  canFlow(t, getLabel(msg), getSkLabel(pk)) == true;
         assert  canFlow(t, getLabel(pk), Public) == true;
         
         flowsToPublicCanFlow(t, getLabel(pk),getLabel(msg));
         flowsToPublicCanFlow(t, getLabel(pk),getSkLabel(pk));
         canFlowTransitive(t, getLabel(pk), getLabel(msg), getSkLabel(pk));

         

    }
    
   else  if(isPublishable(t, msg, pkePred) && isPublishable(t, pk, pkePred)){

    flowsToPublicCanFlow(t, getLabel(msg), getSkLabel(pk));
    assert canFlow(t, getLabel(msg), getSkLabel(pk)) == true;
    
 }
}


lemma void DecryptSatisfiesInvariant<t>(trace<EventParams> tr, Term msg, Term sk, int skOwner)
requires canDecrypt(tr,  encrypt(createPk(sk), msg), sk, skOwner) == true;
ensures wasDecrypted(tr, msg, sk, skOwner) == true;
{
Term pk = createPk(sk);
Label plaintextLabel = getLabel(msg);
Label skLabel = getLabel(sk);

assert isValid(tr, encrypt(createPk(sk), msg), pkePred) == true;


if(pkePred(tr, createPk(sk), msg)){
assert wasDecrypted(tr, msg, sk, skOwner) == true;
}


}
@*/