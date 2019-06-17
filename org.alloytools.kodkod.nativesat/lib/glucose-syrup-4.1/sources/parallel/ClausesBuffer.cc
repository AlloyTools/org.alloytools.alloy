/**********************************************************************************[ClausesBuffer.cc]
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

/* ClausesBuffer
 *
 * This class is responsible for exchanging clauses between threads.
 * It is based on a fixed-length FIFO array of literals.
 * If the FIFO is full, then old clauses are removed (even if it was not yet sent to all threads)
 *
 * a clause " l1 l2 l3" is pushed in the FIFO with the following 6 unsigned integers
 * 3 nseen origin l1 l2 l3
 * + 3 is the size of the pushed clause
 * + nseen is the number of thread which imported this clause (initialized with nthreads-1)
 *       (when set to 0, the clause is removed from the fifo)
 * + origin is the thread id of the thread which added this clause to the fifo
 * + l1 l2 l3 are the literals of the clause
 *
 * **********************************************************************************************
 * **CAREFUL** This class is not thread-safe. In glucose-syrup, the SharedCompanion is 
 * responsible for ensuring atomicity of main functions
 * **********************************************************************************************
 *
 * */

#include "parallel/ClausesBuffer.h"

//=================================================================================================

using namespace Glucose;

extern BoolOption opt_whenFullRemoveOlder;
extern IntOption  opt_fifoSizeByCore;

// index : size clause
// index + 1 : nbSeen
// index + 2 : threadId
// index + 3 : .. index + 3 + size : Lit of clause
ClausesBuffer::ClausesBuffer(int _nbThreads, unsigned int _maxsize) : first(0), last(_maxsize-1),  
    maxsize(_maxsize), queuesize(0), 
    removedClauses(0),
    forcedRemovedClauses(0), nbThreads(_nbThreads), 
    whenFullRemoveOlder(opt_whenFullRemoveOlder), fifoSizeByCore(opt_fifoSizeByCore) {
	lastOfThread.growTo(_nbThreads);
	for(int i=0;i<nbThreads;i++) lastOfThread[i] = _maxsize-1;
	elems.growTo(maxsize);
} 

ClausesBuffer::ClausesBuffer() : first(0), last(0), maxsize(0), queuesize(0), removedClauses(0), forcedRemovedClauses(0), nbThreads(0),
                                 whenFullRemoveOlder(opt_whenFullRemoveOlder), fifoSizeByCore(opt_fifoSizeByCore) {}

void ClausesBuffer::setNbThreads(int _nbThreads) {
    unsigned int _maxsize = fifoSizeByCore*_nbThreads;
    last = _maxsize -1;
    maxsize = _maxsize;
    nbThreads = _nbThreads;
    lastOfThread.growTo(_nbThreads);
    for(int i=0;i<nbThreads;i++) lastOfThread[i] = _maxsize-1;
    elems.growTo(maxsize);
}

uint32_t ClausesBuffer::getCap() {
    return elems.capacity();
}
inline unsigned int ClausesBuffer::nextIndex(unsigned int i) {
    i++;
    if (i == maxsize)
	return 0;
    return i;
}

inline unsigned int ClausesBuffer::addIndex(unsigned int i, unsigned int a) {
    i += a;
    if (i >= maxsize)
	return i - maxsize;
    return i;
}

void ClausesBuffer::removeLastClause() {
    assert(queuesize > 0);
    do {
	unsigned int size = (unsigned int) elems[nextIndex(last)];
	unsigned int nextlast = addIndex(last, size+headerSize);

	for(int i=0;i<nbThreads;i++) {
	    if (lastOfThread[i] == last)
		lastOfThread[i] = nextlast;
	}

	// printf("Removing clause starting at %d of size %d.\n",nextIndex(last), size);
	for(unsigned int i=0;i<size+headerSize;i++) {
	    last = nextIndex(last);
	    assert(queuesize > 0);
	    queuesize --;
	}	
	removedClauses ++;
	assert(last >= 0);
	assert(last < maxsize);
	assert(last == nextlast);
    } while (queuesize > 0 && (elems[addIndex(last,2)] == 0)); 	

}


// Pushes a single uint to the fifo
inline void ClausesBuffer::noCheckPush(uint32_t x) {
    elems[first] = x;
    first = nextIndex(first);
}

// Pops a single uint from the fifo
inline uint32_t ClausesBuffer::noCheckPop(uint32_t & index) {
    index = nextIndex(index);
    uint32_t ret = elems[index];
    return ret;
}



// Return true if the clause was succesfully added
bool ClausesBuffer::pushClause(int threadId, Clause & c) {
    if (!whenFullRemoveOlder && (queuesize + c.size() + headerSize >= maxsize))
	return false; // We need to remove some old clauses
    while (queuesize + c.size() + headerSize >= maxsize) { // We need to remove some old clauses
	forcedRemovedClauses ++;
	removeLastClause();
	assert(queuesize > 0);
    }
    noCheckPush(c.size());
    noCheckPush(nbThreads>1?nbThreads-1:1);
    noCheckPush(threadId);
    for(int i=0;i<c.size();i++)
	noCheckPush(toInt(c[i]));
    queuesize += c.size()+headerSize;
    return true;
    //  printf(" -> (%d, %d)\n", first, last);
}

bool ClausesBuffer::getClause(int threadId, int & threadOrigin, vec<Lit> & resultClause,  bool firstFound) {
    assert(lastOfThread.size() > threadId);
    unsigned int thislast = lastOfThread[threadId];
    assert(!firstFound || thislast == last); // FIXME: Gilles has this assertion on his cluster

    // Early exiting
    if (nextIndex(thislast) == first) return false;

    if ( ( thislast < last && last < first) ||
	    ( first < thislast && thislast < last ) ||
	    ( last < first && first < thislast) ) {
	// Special case where last has moved and lastOfThread[threadId] is no more valid (is behind)
	thislast = last; 
    }
    assert(!firstFound);
    // Go to next clause for this thread id
    if (!firstFound) { 
	while (nextIndex(thislast) != first && elems[addIndex(thislast,3)] == ((unsigned int)threadId)) { // 3 = 2 + 1 
	    thislast = addIndex(thislast, elems[nextIndex(thislast)] + headerSize); // 
	    assert(thislast >= 0);
	    assert(thislast < maxsize);
	}
	assert(nextIndex(thislast)==first || elems[addIndex(thislast,3)] != (unsigned int)threadId);
    }

    if (nextIndex(thislast) == first) {
	lastOfThread[threadId] = thislast;
	return false;
    }  
    assert(elems[addIndex(thislast,3)] != ((unsigned int) threadId));
    unsigned int previouslast = thislast;
    bool removeAfter = false;
    int csize = noCheckPop(thislast);
    removeAfter = (--elems[addIndex(thislast,1)] == 0); // We are sure this is not one of our own clause
    thislast = nextIndex(thislast); // Skips the removeAfter fieldr
    threadOrigin = noCheckPop(thislast);
    assert(threadOrigin != threadId);
    resultClause.clear();
    for(int i=0;i<csize;i++) {
	resultClause.push(toLit(noCheckPop(thislast)));
    }
    if (last == previouslast && removeAfter) {
	removeLastClause();
	thislast = last;
    }
    lastOfThread[threadId] = thislast;
    return true;
}


//=================================================================================================

