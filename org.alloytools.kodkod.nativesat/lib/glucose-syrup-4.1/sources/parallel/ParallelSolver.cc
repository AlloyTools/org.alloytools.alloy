/***************************************************************************************[ParallelSolver.cc]
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

#include "parallel/ParallelSolver.h"
#include "mtl/Sort.h"

using namespace Glucose;

//=====================================================================
// == Options

const char* _cunstable = "CORE/PARALLEL -- UNSTABLE FEATURES";
const char* _parallel = "PARALLEL";

extern BoolOption opt_dontExportDirectReusedClauses; // (_cunstable, "reusedClauses",    "Don't export directly reused clauses", false);
extern BoolOption opt_plingeling; // (_cunstable, "plingeling",    "plingeling strategy for sharing clauses (exploratory feature)", false);

//=====================================================================

//=====================================================================


ParallelSolver::ParallelSolver(int threadId) :
  SimpSolver()
, thn(threadId) // The thread number of this solver
, goodlimitlbd(7)
, goodlimitsize(25)
, purgatory(true)
, shareAfterProbation(!opt_plingeling) // only share clauses after probation 
, plingeling(opt_plingeling)
, nbTimesSeenBeforeExport(2)
, firstSharing(5000) // Strong limit : do not share anything (except unary clauses) before this number of conflicts
, limitSharingByGoodLBD(true) // Moving limit of what a good LBD is (median value of last learnt clauses set)
, limitSharingByFixedLimitLBD(0) // No fixed bound (like 8 in plingeling)
, limitSharingByFixedLimitSize(0) // No fixed boud (like 40 in plingeling) 
, dontExportDirectReusedClauses(opt_dontExportDirectReusedClauses)
, nbNotExportedBecauseDirectlyReused(0)
{
    useUnaryWatched = true; // We want to use promoted clauses here !
    stats.growTo(parallelStatsSize,0);
}




ParallelSolver::~ParallelSolver() {
    printf("c Solver of thread %d ended.\n", thn);
    fflush(stdout);
}

ParallelSolver::ParallelSolver(const ParallelSolver &s) : 
    SimpSolver(s)
    , sharedcomp(s.sharedcomp)
, goodlimitlbd(s.goodlimitlbd)
, goodlimitsize(s.goodlimitsize)
, purgatory(s.purgatory)
, shareAfterProbation(s.shareAfterProbation) // only share clauses after probation 
, plingeling(s.plingeling)
,nbTimesSeenBeforeExport(2)
, firstSharing(s.firstSharing) // Strong limit : do not share anything (except unary clauses) before this number of conflicts
, limitSharingByGoodLBD(s.limitSharingByGoodLBD) // Moving limit of what a good LBD is (median value of last learnt clauses set)
, limitSharingByFixedLimitLBD(s.limitSharingByFixedLimitLBD) // No fixed bound (like 8 in plingeling)
, limitSharingByFixedLimitSize(s.limitSharingByFixedLimitSize) // No fixed boud (like 40 in plingeling) 
, dontExportDirectReusedClauses(s.dontExportDirectReusedClauses)
, nbNotExportedBecauseDirectlyReused(s.nbNotExportedBecauseDirectlyReused) 
{
    s.goodImportsFromThreads.memCopyTo(goodImportsFromThreads);   
    useUnaryWatched = s.useUnaryWatched;
    s.stats.copyTo(stats);
    s.elimclauses.copyTo(elimclauses); // This should be done more efficiently some day
}


// Strategy to reduce unary watches list
struct reduceDB_oneWatched_lt {
    ClauseAllocator& ca;

    reduceDB_oneWatched_lt(ClauseAllocator& ca_) : ca(ca_) {
    }

    bool operator()(CRef x, CRef y) {

        // Main criteria... Like in MiniSat we keep all binary clauses
        if (ca[x].size() > 2 && ca[y].size() == 2) return 1;

        if (ca[y].size() > 2 && ca[x].size() == 2) return 0;
        if (ca[x].size() == 2 && ca[y].size() == 2) return 0;

        // Second one  based on literal block distance
        if (ca[x].size() > ca[y].size()) return 1;
        if (ca[x].size() < ca[y].size()) return 0;

        if (ca[x].lbd() > ca[y].lbd()) return 1;
        if (ca[x].lbd() < ca[y].lbd()) return 0;

        // Finally we can use old activity or size, we choose the last one
        return ca[x].activity() < ca[y].activity();
        //return x->size() < y->size();

        //return ca[x].size() > 2 && (ca[y].size() == 2 || ca[x].activity() < ca[y].activity()); } 
    }
};

// @overide
void ParallelSolver::reduceDB() {

    int i, j;
    stats[nbReduceDB]++;
    
    int limit;

  if (chanseokStrategy)
      sort(learnts, reduceDBAct_lt(ca));
  else 
      sort(learnts, reduceDB_lt(ca));

  if (!chanseokStrategy && !panicModeIsEnabled()) {
        // We have a lot of "good" clauses, it is difficult to compare them. Keep more !
        if (ca[learnts[learnts.size() / RATIOREMOVECLAUSES]].lbd() <= 3) nbclausesbeforereduce += specialIncReduceDB;
        // Useless :-)
        if (ca[learnts.last()].lbd() <= 5) nbclausesbeforereduce += specialIncReduceDB;
  }
        // Don't delete binary or locked clauses. From the rest, delete clauses from the first half
        // Keep clauses which seem to be usefull (their lbd was reduce during this sequence)

  if (!panicModeIsEnabled()) {
        limit = learnts.size() / 2;
    } else {
        limit = panicModeLastRemoved;
    }
    panicModeLastRemoved = 0;

    uint64_t sumsize = 0;
    for (i = j = 0; i < learnts.size(); i++) {

        Clause& c = ca[learnts[i]];
        if (i == learnts.size() / 2)
            goodlimitlbd = c.lbd();
        sumsize += c.size();
        if (c.lbd() > 2 && c.size() > 2 && c.canBeDel() && !locked(c) && (i < limit)) {
            removeClause(learnts[i]);
            stats[nbRemovedClauses]++;
            panicModeLastRemoved++;
        } else {
            if (!c.canBeDel()) limit++; //we keep c, so we can delete an other clause
            c.setCanBeDel(true); // At the next step, c can be delete
            learnts[j++] = learnts[i];
        }
    }
    learnts.shrink(i - j);

    if (learnts.size() > 0)
        goodlimitsize = 1 + (double) sumsize / (double) learnts.size();

    // Special treatment for imported clauses
    if (!panicModeIsEnabled())
        limit = unaryWatchedClauses.size() - (learnts.size() * (chanseokStrategy?4:2));
    else
        limit = panicModeLastRemovedShared;
    panicModeLastRemovedShared = 0;
    if ((unaryWatchedClauses.size() > 100) && (limit > 0)) {

        sort(unaryWatchedClauses, reduceDB_oneWatched_lt(ca));

        for (i = j = 0; i < unaryWatchedClauses.size(); i++) {
            Clause& c = ca[unaryWatchedClauses[i]];
            if (c.lbd() > 2 && c.size() > 2 && c.canBeDel() && !locked(c) && (i < limit)) {
                removeClause(unaryWatchedClauses[i], c.getOneWatched()); // remove from the purgatory (or not)
                stats[nbRemovedUnaryWatchedClauses]++;
                panicModeLastRemovedShared++;
            } else {
                if (!c.canBeDel()) limit++; //we keep c, so we can delete an other clause
                c.setCanBeDel(true); // At the next step, c can be delete
                unaryWatchedClauses[j++] = unaryWatchedClauses[i];
            }
        }
        unaryWatchedClauses.shrink(i - j);
    }

    checkGarbage();
}


/*_________________________________________________________________________________________________
|
|  parallelImportClauseDuringConflictAnalysis : (Clause &c,CRef confl)   ->  [void]
|  
|  Description:
|    Verify if the clause using during conflict analysis is good for export
|    @see : analyze
|  Output:
|________________________________________________________________________________________________@*/


void ParallelSolver::parallelImportClauseDuringConflictAnalysis(Clause &c,CRef confl) {
    if (dontExportDirectReusedClauses && (confl == lastLearntClause) && (c.getExported() < nbTimesSeenBeforeExport)) { // Experimental stuff
        c.setExported(nbTimesSeenBeforeExport);
        nbNotExportedBecauseDirectlyReused++;
    } else if (shareAfterProbation && c.getExported() != nbTimesSeenBeforeExport && conflicts > firstSharing) {
        c.setExported(c.getExported() + 1);
        if (!c.wasImported() && c.getExported() == nbTimesSeenBeforeExport) { // It's a new interesting clause: 
            if (c.lbd() == 2 || (c.size() < goodlimitsize && c.lbd() <= goodlimitlbd)) {
                shareClause(c);
            }
        }
    }

}



// These Two functions are useless here !!
void ParallelSolver::reportProgress() {
    printf("c | %2d | %6d | %10d | %10d | %8d | %8d | %8d | %8d | %8d | %6.3f |\n",(int)thn,(int)starts,(int)decisions,(int)conflicts,(int)stats[originalClausesSeen],(int)learnts.size(),(int)stats[nbexported],(int)stats[nbimported],(int)stats[nbPromoted],progressEstimate()*100);

    //printf("c thread=%d confl=%lld starts=%llu reduceDB=%llu learnts=%d broadcast=%llu  blockedReuse=%lld imported=%llu promoted=%llu limitlbd=%llu limitsize=%llu\n", thn, conflicts, starts, nbReduceDB, learnts.size(), nbexported, nbNotExportedBecauseDirectlyReused, nbimported, nbPromoted, goodlimitlbd, goodlimitsize);
}

void ParallelSolver::reportProgressArrayImports(vec<unsigned int> &totalColumns) {
    return ; // TODO : does not currently work
    unsigned int totalImports = 0;
    printf("c %3d | ", thn);
    for (int i = 0; i <  sharedcomp->nbThreads; i++) {
        totalImports += goodImportsFromThreads[i];
        totalColumns[i] += goodImportsFromThreads[i];
        printf(" %8d", goodImportsFromThreads[i]);
    }
    printf(" | %8d\n", totalImports);

}
 


/*_________________________________________________________________________________________________
|
|  shareClause : (Clause &c)   ->  [bool]
|  
|  Description:
|  share a clause to other cores  
| @see : analyze
|  Output: true if the clause is indeed sent
|________________________________________________________________________________________________@*/

bool ParallelSolver::shareClause(Clause & c) {
    bool sent = sharedcomp->addLearnt(this, c);
    if (sent)
        stats[nbexported]++;
    return sent;
}

/*_________________________________________________________________________________________________
|
|  panicModeIsEnabled : ()   ->  [bool]
|  
|  Description:
|  is panic mode (save memory) is enabled ?
|________________________________________________________________________________________________@*/

bool ParallelSolver::panicModeIsEnabled() {
    return sharedcomp->panicMode;
}

/*_________________________________________________________________________________________________
|
|  parallelImportUnaryClauses : ()   ->  [void]
|  
|  Description:
|  import all unary clauses from other cores
|________________________________________________________________________________________________@*/

void ParallelSolver::parallelImportUnaryClauses() {
    Lit l;
    while ((l = sharedcomp->getUnary(this)) != lit_Undef) {
        if (value(var(l)) == l_Undef) {
            uncheckedEnqueue(l);
            stats[nbimportedunit]++;
        }
    }
}

/*_________________________________________________________________________________________________
|
|  parallelImportClauses : ()   ->  [bool]
|  
|  Description:
|  import all clauses from other cores
|  Output : if there is a final conflict
|________________________________________________________________________________________________@*/

bool ParallelSolver::parallelImportClauses() {

    assert(decisionLevel() == 0);
    int importedFromThread;
    while (sharedcomp->getNewClause(this, importedFromThread, importedClause)) {
        assert(importedFromThread <= sharedcomp->nbThreads);
        assert(importedFromThread >= 0);

        assert(importedFromThread != thn);

        if (importedClause.size() == 0)
            return true;

        //printf("Thread %d imports clause from thread %d\n", threadNumber(), importedFromThread);
        CRef cr = ca.alloc(importedClause, true, true);
        ca[cr].setLBD(importedClause.size());
        if (plingeling) // 0 means a broadcasted clause (good clause), 1 means a survivor clause, broadcasted
            ca[cr].setExported(2); // A broadcasted clause (or a survivor clause) do not share it anymore
        else {
            ca[cr].setExported(1); // next time we see it in analyze, we share it (follow route / broadcast depending on the global strategy, part of an ongoing experimental stuff: a clause in one Watched will be set to exported 2 when promotted.
        }
        ca[cr].setImportedFrom(importedFromThread);
        if(useUnaryWatched)
            unaryWatchedClauses.push(cr);
        else 
            learnts.push(cr);
        
        if (plingeling || ca[cr].size() <= 2) {//|| importedRoute == 0) { // importedRoute == 0 means a glue clause in another thread (or any very good clause)
            ca[cr].setOneWatched(false); // Warning: those clauses will never be promoted by a conflict clause (or rarely: they are propagated!)
            attachClause(cr);
            stats[nbImportedGoodClauses]++;
        } else {
            if(useUnaryWatched) {
                attachClausePurgatory(cr); // 
                ca[cr].setOneWatched(true);
            } else {
                attachClause(cr);
                ca[cr].setOneWatched(false);
            }
            stats[nbimportedInPurgatory]++;
        }
        assert(ca[cr].learnt());
        stats[nbimported]++;
    }
    return false;
}


/*_________________________________________________________________________________________________
|
|  parallelExportUnaryClause : (Lit p)   ->  [void]
|  
|  Description:
|  export unary clauses to other cores
|________________________________________________________________________________________________@*/

void ParallelSolver::parallelExportUnaryClause(Lit p) {
    // Multithread
    sharedcomp->addLearnt(this,p ); // TODO: there can be a contradiction here (two theads proving a and -a)
    stats[nbexportedunit]++;
}


/*_________________________________________________________________________________________________
|
|  parallelExportClauseDuringSearch : (Clause &c)   ->  [void]
|  
|  Description:
|  Verify if a new learnt clause is useful for export
|  @see search
|  
|________________________________________________________________________________________________@*/

void ParallelSolver::parallelExportClauseDuringSearch(Clause &c) {
    //
    // Multithread
    // Now I'm sharing the clause if seen in at least two conflicts analysis shareClause(ca[cr]);
    if ((plingeling && !shareAfterProbation && c.lbd() < 8 && c.size() < 40) ||
            (c.lbd() <= 2)) { // For this class of clauses, I'm sharing them asap (they are Glue CLauses, no probation for them)
        shareClause(c);
        c.setExported(2);
    }

}


/*_________________________________________________________________________________________________
|
|  parallelJobIsFinished : ()   ->  [bool]
|  
|  Description:
|  Is a core already finish the search
|  
|________________________________________________________________________________________________@*/

bool ParallelSolver::parallelJobIsFinished() { 
    // Parallel: another job has finished let's quit
    return (sharedcomp->jobFinished());
}

// @overide
lbool ParallelSolver::solve_(bool do_simp, bool turn_off_simp) {
       vec<Var> extra_frozen;
    lbool    result = l_True;
    do_simp &= use_simplification;
    if (do_simp){
        // Assumptions must be temporarily frozen to run variable elimination:
        for (int i = 0; i < assumptions.size(); i++){
            Var v = var(assumptions[i]);

            // If an assumption has been eliminated, remember it.
            assert(!isEliminated(v));

            if (!frozen[v]){
                // Freeze and store.
                setFrozen(v, true);
                extra_frozen.push(v);
            } }

        result = lbool(eliminate(turn_off_simp));
    }

    model.clear();
    conflict.clear();
    if (!ok) return l_False;

    solves++;


    lbool status = l_Undef;

    // Search:
    int curr_restarts = 0;
    while (status == l_Undef && !sharedcomp->jobFinished()) {
        status = search(luby_restart?luby(restart_inc, curr_restarts)*luby_restart_factor:0);  // the parameter is useless in glucose, kept to allow modifications
        if (!withinBudget()) break;
        curr_restarts++;
    }

    if (verbosity >= 1)
        printf("c =========================================================================================================\n");

/*
    if (do_simp)
        // Unfreeze the assumptions that were frozen:
        for (int i = 0; i < extra_frozen.size(); i++)
            setFrozen(extra_frozen[i], false);
*/
    
    bool firstToFinish = false;
    if (status != l_Undef)
        firstToFinish = sharedcomp->IFinished(this);
    if (firstToFinish) {
        printf("c Thread %d is 100%% pure glucose! First thread to finish! (%s answer).\n", threadNumber(), status == l_True ? "SAT" : status == l_False ? "UNSAT" : "UNKOWN");
        sharedcomp->jobStatus = status;
    }
    
    if (firstToFinish && status == l_True) {
        extendModel();


        // Extend & copy model:
        model.growTo(nVars());
        for (int i = 0; i < nVars(); i++) model[i] = value(i);
    } else if (status == l_False && conflict.size() == 0)
        ok = false;


    pthread_cond_signal(pcfinished);

    //cancelUntil(0);


    return status;

}
