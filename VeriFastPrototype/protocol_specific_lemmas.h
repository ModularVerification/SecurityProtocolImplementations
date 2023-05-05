#ifndef PROTOCOL_SPECIFIC_LEMMAS
#define PROTOCOL_SPECIFIC_LEMMAS
#include "definitions.h"
#include "term_definition.h"
#include "ghost_trace.h"

// this file declares the lemmas that must be shown by a protocol after instantiating
// this library

/*@
lemma void pkeMonotonic(Trace t1, Trace t2, Term ptxt, Term pk);
requires individual_snapshot_suffix(t1, t2) == true && pkePred(t1, ptxt, pk) == true;
ensures pkePred(t2,  ptxt, pk) == true;
@*/
#endif
