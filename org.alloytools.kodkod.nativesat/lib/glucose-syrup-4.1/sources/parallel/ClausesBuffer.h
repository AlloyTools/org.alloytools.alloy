/***************************************************************************************[ClausesBuffer.h]
 Glucose -- Copyright (c) 2009-2014, Gilles Audemard, Laurent Simon
                                CRIL - Univ. Artois, France
                                LRI  - Univ. Paris Sud, France (2009-2013)
                                Labri - Univ. Bordeaux, France

 Syrup (Glucose Parallel) -- Copyright (c) 2013-2014, Gilles Audemard, Laurent Simon
                                CRIL - Univ. Artois, France
                                Labri - Univ. Bordeaux, France

Glucose sources are based on MiniSat (see below MiniSat copyrights). Permissions and copyrights of
Glucose (sources until 2013, Glucose 3.0, single core) are exactly the same as Minisat on which it 
is based on. (see below).

Glucose-Syrup sources are based on another copyright. Permissions and copyrights for the parallel
version of Glucose-Syrup (the "Software") are granted, free of charge, to deal with the Software
without restriction, including the rights to use, copy, modify, merge, publish, distribute,
sublicence, and/or sell copies of the Software, and to permit persons to whom the Software is 
furnished to do so, subject to the following conditions:

- The above and below copyrights notices and this permission notice shall be included in all
copies or substantial portions of the Software;
- The parallel version of Glucose (all files modified since Glucose 3.0 releases, 2013) cannot
be used in any competitive event (sat competitions/evaluations) without the express permission of 
the authors (Gilles Audemard / Laurent Simon). This is also the case for any competitive event
using Glucose Parallel as an embedded SAT engine (single core or not).


--------------- Original Minisat Copyrights

Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

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

#ifndef ClausesBuffer_h 
#define ClausesBuffer_h

#include "mtl/Vec.h"
#include "core/SolverTypes.h"
#include "core/Solver.h"

//=================================================================================================

namespace Glucose {
    // index : size clause
    // index + 1 : nbSeen
    // index + 2 : threadId
    // index + 3 : .. index + 3 + size : Lit of clause
    class ClausesBuffer {
	vec<uint32_t>  elems;
	unsigned int     first;
	unsigned int	 last;
	unsigned int     maxsize;
	unsigned int     queuesize; // Number of current elements (must be < maxsize !)
	unsigned int     removedClauses;
	unsigned int     forcedRemovedClauses;
        static const int  headerSize = 3;
	int       nbThreads;
	bool      whenFullRemoveOlder;
	unsigned int fifoSizeByCore;
	vec<unsigned int> lastOfThread; // Last value for a thread 

	public:
	ClausesBuffer(int _nbThreads, unsigned int _maxsize);
	ClausesBuffer();

	void setNbThreads(int _nbThreads);
	unsigned int nextIndex(unsigned int i);
	unsigned int addIndex(unsigned int i, unsigned int a); 
	void removeLastClause(); 
	   
	void noCheckPush(uint32_t x);
	uint32_t noCheckPop(unsigned int & index);

	// Return true if the clause was succesfully added
        bool pushClause(int threadId, Clause & c);
        bool getClause(int threadId, int & threadOrigin, vec<Lit> & resultClause, bool firstFound = false); 
	
	int maxSize() const {return maxsize;}
        uint32_t getCap();
	void growTo(int size) {
	    assert(0); // Not implemented (essentially for efficiency reasons)
	    elems.growTo(size); 
	    first=0; maxsize=size; queuesize = 0;last = 0;
	    for(int i=0;i<size;i++) elems[i]=0; 
	}

	void fastclear() {first = 0; last = 0; queuesize=0; } 

	int  size(void)    { return queuesize; }

	void clear(bool dealloc = false)   { elems.clear(dealloc); first = 0; maxsize=0; queuesize=0;}
	inline  int  toInt     (Lit p)              { return p.x; } 

    };
}
//=================================================================================================

#endif
