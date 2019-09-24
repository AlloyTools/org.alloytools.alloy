/**************************************************************************************[ParallelSolver.h]
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

#ifndef PARALLELSOLVER_H
#define	PARALLELSOLVER_H

#include "core/SolverTypes.h"
#include "core/Solver.h"
#include "simp/SimpSolver.h"
#include "parallel/SharedCompanion.h"
namespace Glucose {
    
   enum ParallelStats{
       nbexported=coreStatsSize,
       nbimported,
       nbexportedunit,
       nbimportedunit,
       nbimportedInPurgatory,
       nbImportedGoodClauses
   } ;
#define parallelStatsSize (coreStatsSize + 6)
 
//=================================================================================================
    //class MultiSolvers;
    //class SolverCompanion;
 //   class MultiSolvers;
    
class ParallelSolver : public SimpSolver {
    friend class MultiSolvers;
    friend class SolverCompanion;
    friend class SharedCompanion;
//    friend class ReasoningCompanion;
//    friend class SolverConfiguration;

protected : 
          // Multithread :
    int		thn; // internal thread number
    //MultiSolvers* belongsto; // Not working (due to incomplete types)
    SharedCompanion *sharedcomp;
    bool coreFUIP; // true if one core is specialized for branching on all FUIP
    bool ImTheSolverFUIP;
    pthread_mutex_t *pmfinished; // mutex on which main process may wait for... As soon as one process finishes it release the mutex
    pthread_cond_t *pcfinished; // condition variable that says that a thread as finished

public:
    // Constructor/Destructor:
    //
    ParallelSolver(int threadId);
    ParallelSolver(const ParallelSolver &s);
    ~ParallelSolver();
    
    /**
     * Clone function
     */
    virtual Clone* clone() const {
        return  new ParallelSolver(*this);
    }   

    int  threadNumber  ()      const;
    void setThreadNumber (int i);
    void reportProgress();
    void reportProgressArrayImports(vec<unsigned int> &totalColumns);
    virtual void reduceDB();
    virtual lbool         solve_                   (bool do_simp = true, bool turn_off_simp = false);

    vec<Lit>    importedClause; // Temporary clause used to copy each imported clause
    unsigned int    goodlimitlbd; // LBD score of the "good" clauses, locally
    int    goodlimitsize;
    bool purgatory; // mode of operation
    bool shareAfterProbation; // Share any none glue clause only after probation (seen 2 times in conflict analysis)
    bool plingeling; // plingeling strategy for sharing clauses (experimental)
    int nbTimesSeenBeforeExport;
    // Stats front end
//    uint64_t   getNbExported() { return nbexported;}
 //   uint64_t   getNbImported() { return nbimported;}
 //   uint64_t   getNbExportedUnit() {return nbexportedunit;}
    
    uint32_t  firstSharing, limitSharingByGoodLBD, limitSharingByFixedLimitLBD, limitSharingByFixedLimitSize;
    uint32_t  probationByFollowingRoads, probationByFriend;
    uint32_t  survivorLayers; // Number of layers for a common clause to survive
    bool dontExportDirectReusedClauses ; // When true, directly reused clauses are not exported
    uint64_t nbNotExportedBecauseDirectlyReused;
    
    
    vec<uint32_t> goodImportsFromThreads; // Stats of good importations from other threads

    virtual void parallelImportClauseDuringConflictAnalysis(Clause &c,CRef confl);
    virtual bool parallelImportClauses(); // true if the empty clause was received
    virtual void parallelImportUnaryClauses();
    virtual void parallelExportUnaryClause(Lit p);
    virtual void parallelExportClauseDuringSearch(Clause &c);
    virtual bool parallelJobIsFinished();
    virtual bool panicModeIsEnabled();
 
    bool shareClause(Clause & c); // true if the clause was succesfully sent

    

};


    inline int      ParallelSolver::threadNumber  ()      const   {return thn;}
    inline void     ParallelSolver::setThreadNumber (int i)       {thn = i;}
}
#endif	/* PARALLELSOLVER_H */

