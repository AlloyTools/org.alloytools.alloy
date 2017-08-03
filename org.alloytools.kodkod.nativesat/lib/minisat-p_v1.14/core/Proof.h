/*****************************************************************************************[Proof.h]
MiniSat -- Copyright (c) 2003-2005, Niklas Een, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#ifndef Proof_h
#define Proof_h

#include "SolverTypes.h"
#include "File.h"


//=================================================================================================


// A "listner" for the proof. Proof events will be passed onto (online mode) or replayed to
// (offline mode) this class.  Each call to 'root()' or 'chain()' produces a new clause. The first
// clause has ID 0, the next 1 and so on. These are the IDs passed to 'chain()'s 'cs' parameter.
//
struct ProofTraverser {
    virtual void root   (const vec<Lit>& c) {}
    virtual void chain  (const vec<ClauseId>& cs, const vec<Var>& xs) {}
    virtual void deleted(ClauseId c) {}
    virtual void done   () {}
    virtual ~ProofTraverser() {}
};


class Proof {
    File            fp;
    cchar*          fp_name;
    ClauseId        id_counter;
    ProofTraverser* trav;

    vec<Lit>        clause;
    vec<ClauseId>   chain_id;
    vec<Var>        chain_var;

public:
    Proof();                        // Offline mode -- proof stored to a file, which can be saved, compressed, and/or traversed.
    Proof(ProofTraverser& t);       // Online mode -- proof will not be stored.  							
    
    ClauseId addRoot   (vec<Lit>& clause);
    void     beginChain(ClauseId start);
    void     resolve   (ClauseId next, Var x);
    ClauseId endChain  ();
    void     deleted   (ClauseId gone);
    ClauseId last      () { assert(id_counter != ClauseId_NULL); return id_counter - 1; }
	ClauseId next      () { return id_counter; }
    void     compress  (Proof& dst, ClauseId goal = ClauseId_NULL);     // 'dst' should be a newly constructed, empty proof.
    bool     save      (cchar* filename);
    void     traverse  (ProofTraverser& trav, ClauseId goal = ClauseId_NULL) ;
};


//=================================================================================================
#endif
