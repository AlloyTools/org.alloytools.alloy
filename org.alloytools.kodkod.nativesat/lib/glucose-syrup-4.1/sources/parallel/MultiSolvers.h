/***************************************************************************************[MultiSolvers.h]
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

#ifndef MultiSolvers_h
#define MultiSolvers_h

#include "parallel/ParallelSolver.h"

namespace Glucose {
    class SolverConfiguration;
    
class MultiSolvers {
    friend class SolverConfiguration;

public:
  MultiSolvers(ParallelSolver *s);
  MultiSolvers();
  ~MultiSolvers();
 
  void printFinalStats(); 

  void setVerbosity(int i);
  int verbosity();
  void setVerbEveryConflicts(int i);
  void setShowModel(int i) {showModel = i;}
  int getShowModel() {return showModel;}
  // Problem specification:
  //
  Var     newVar    (bool polarity = true, bool dvar = true); // Add a new variable with parameters specifying variable mode.
  bool    addClause (const vec<Lit>& ps);                           // Add a clause to the solver. NOTE! 'ps' may be shrunk by this method!
  bool    addClause_(      vec<Lit>& ps);       
  
  bool    simplify     ();                        // Removes already satisfied clauses.
  
  int     nVars      ()      const;       // The current number of variables.
  int     nClauses      ()      const;       // The current number of variables.
  ParallelSolver *getPrimarySolver();
  
  void generateAllSolvers();
  
  // Solving:
  //
  lbool    solve        ();                        // Search without assumptions.
  bool eliminate();             // Perform variable elimination
  void adjustParameters();
  void adjustNumberOfCores();
  void interrupt() {}
  vec<lbool> model;             // If problem is satisfiable, this vector contains the model (if any).
  inline bool okay() {
    if(!ok) return ok;
    for(int i = 0;i<solvers.size();i++) {
	if(!((SimpSolver*)solvers[i])->okay()) {
	    ok = false;
	    return false;
	}
    }
    return true;
 
  }

  bool use_simplification;

  
 protected:
	friend class ParallelSolver;
	friend class SolverCompanion;
	
struct Stats {
    uint64_t min, max, avg, std, med;
    Stats(uint64_t _min = 0,uint64_t _max = 0,uint64_t  _avg = 0,uint64_t  _std = 0,uint64_t  _med = 0) : 
	min(_min), max(_max), avg(_avg), std(_std), med(_med) {} 
};

	void printStats(); 
	int ok;
	lbool result;
	int maxnbthreads; // Maximal number of threads
	int nbthreads; // Current number of threads
	int nbsolvers; // Number of CDCL solvers
	int nbcompanions; // Number of companions
	int nbcompbysolver; // Number of companions by solvers
	bool immediateSharingGlue ;
	int allClonesAreBuilt;
        bool showModel; // show model on/off

	int winner;

    vec<Lit>            add_tmp;
 	
    double    var_decay;          // Inverse of the variable activity decay factor.                                            (default 1 / 0.95)
    double    clause_decay;       // Inverse of the clause activity decay factor.                                              (1 / 0.999)
    double    cla_inc;          // Amount to bump next clause with.
    double    var_inc;          // Amount to bump next variable with.	
    double    random_var_freq;    // The frequency with which the decision heuristic tries to choose a random variable.        (default 0.02)
    int       restart_first;      // The initial restart limit.                                                                (default 100)
    double    restart_inc;        // The factor with which the restart limit is multiplied in each restart.                    (default 1.5)
    double    learntsize_factor;  // The intitial limit for learnt clauses is a factor of the original clauses.                (default 1 / 3)
    double    learntsize_inc;     // The limit for learnt clauses is multiplied with this factor each restart.                 (default 1.1)
    bool      expensive_ccmin;    // Controls conflict clause minimization.                                                    (default TRUE)
    int       polarity_mode;      // Controls which polarity the decision heuristic chooses. See enum below for allowed modes. (default polarity_false)
    unsigned int maxmemory;
    unsigned int maxnbsolvers;
    int verb; 
    int verbEveryConflicts;
    int numvar; // Number of variables
    int numclauses; // Number of clauses

    enum { polarity_true = 0, polarity_false = 1, polarity_user = 2, polarity_rnd = 3 };

   //ClauseAllocator     ca;
   SharedCompanion * sharedcomp;

    void informEnd(lbool res);
    ParallelSolver* retrieveSolver(int i);

    pthread_mutex_t m; // mutex for any high level sync between all threads (like reportf)
    pthread_mutex_t mfinished; // mutex on which main process may wait for... As soon as one process finishes it release the mutex
    pthread_cond_t cfinished; // condition variable that says that a thread has finished
	
    vec<ParallelSolver*> solvers; // set of plain solvers
    vec<SolverCompanion*> solvercompanions; // set of companion solvers
    vec<pthread_t*> threads; // all threads of this process
    vec<int> threadIndexOfSolver; // threadIndexOfSolver[solvers[i]] is the index in threads[] of the solver i
    vec<int> threadIndexOfSolverCompanion; // threadIndexOfSolverCompanion[solvercompanions[i]] is the index in threads[] of the solvercompanion i
};

inline bool     MultiSolvers::addClause       (const vec<Lit>& ps)    { ps.copyTo(add_tmp); return addClause_(add_tmp); }

inline void MultiSolvers::setVerbosity(int i) {verb = i;}
inline void MultiSolvers::setVerbEveryConflicts(int i) {verbEveryConflicts=i;}
inline int      MultiSolvers::nVars         ()      const   { return numvar; }
inline int      MultiSolvers::nClauses      ()      const   { return numclauses; }
inline int MultiSolvers::verbosity()  {return verb;}
inline ParallelSolver* MultiSolvers::getPrimarySolver() {return solvers[0];}


}
#endif

