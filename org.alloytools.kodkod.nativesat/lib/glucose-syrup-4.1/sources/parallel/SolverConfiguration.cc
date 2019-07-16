/***************************************************************************************[SolverConfiguration.cc]
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

#include "parallel/MultiSolvers.h"
#include "core/Solver.h"
//#include "parallel/ParallelSolver.h"
#include "parallel/SolverConfiguration.h"

using namespace Glucose;


void SolverConfiguration::configure(MultiSolvers *ms, int nbsolvers) {
    for(int i = 1;i<nbsolvers;i++) { // Configuration for the sat race 2015
        ms->solvers[i]->randomizeFirstDescent = true;
        ms->solvers[i]->adaptStrategies = (i%2==0); // Just half of the cores are in adaptive mode
        ms->solvers[i]->forceUnsatOnNewDescent = (i%4==0); // Just half of adaptive cores have the unsat force
    }
    if (nbsolvers > 8) { // configuration for the second phase of the sat race 2015
        for(int i=0;i<nbsolvers;i++) { // we have like 32 threads, so we need to export just very good clauses
            ms->solvers[i]->goodlimitlbd = 5;
            ms->solvers[i]->goodlimitsize = 15;
        }
    }

}

        
void SolverConfiguration::configureSAT15Adapt(MultiSolvers *ms, int nbsolvers) {
    for(int i = 1;i<nbsolvers;i++) { // Configuration for the sat race 2015
        ms->solvers[i]->randomizeFirstDescent = true;
        ms->solvers[i]->adaptStrategies = (i%2==0); // Just half of the cores are in adaptive mode
    }
    if (nbsolvers > 8) { // configuration for the second phase of the sat race 2015
        for(int i=0;i<nbsolvers;i++) { // we have like 32 threads, so we need to export just very good clauses
            ms->solvers[i]->goodlimitlbd = 5;
            ms->solvers[i]->goodlimitsize = 15;
        }
    }
}


void SolverConfiguration::configureSAT15Default(MultiSolvers *ms, int nbsolvers) {
    for(int i = 1;i<nbsolvers;i++) 
	ms->solvers[i]->randomizeFirstDescent = true;

    if (nbsolvers > 8) { // configuration for the second phase of the sat race 2015
	for(int i=0;i<nbsolvers;i++) { 
	    ms->solvers[i]->goodlimitlbd = 5;
	    ms->solvers[i]->goodlimitsize = 15;

	}
    }

}

void SolverConfiguration::configureSAT14(MultiSolvers *ms, int nbsolvers) {
    
   if (nbsolvers < 2 ) return;

   ms->solvers[1]->var_decay = 0.94;
   ms->solvers[1]->max_var_decay = 0.96;
   ms->solvers[1]->firstReduceDB=600;

   if (nbsolvers < 3 ) return;

   ms->solvers[2]->var_decay = 0.90;
   ms->solvers[2]->max_var_decay = 0.97;
   ms->solvers[2]->firstReduceDB=500;

   if (nbsolvers < 4 ) return;

   ms->solvers[3]->var_decay = 0.85;
   ms->solvers[3]->max_var_decay = 0.93;
   ms->solvers[3]->firstReduceDB=400;

   if (nbsolvers < 5 ) return;

   // Glucose 2.0 (+ blocked restarts)
   ms->solvers[4]->var_decay = 0.95;
   ms->solvers[4]->max_var_decay = 0.95;
   ms->solvers[4]->firstReduceDB=4000;
   ms->solvers[4]->lbdQueue.growTo(100);
   ms->solvers[4]->sizeLBDQueue = 100;
   ms->solvers[4]->K = 0.7;
   ms->solvers[4]->incReduceDB = 500;

   if (nbsolvers < 6 ) return;

   ms->solvers[5]->var_decay = 0.93;
   ms->solvers[5]->max_var_decay = 0.96;
   ms->solvers[5]->firstReduceDB=100;
   ms->solvers[5]->incReduceDB = 500;

   if (nbsolvers < 7 ) return;

   ms->solvers[6]->var_decay = 0.75;
   ms->solvers[6]->max_var_decay = 0.94;
   ms->solvers[6]->firstReduceDB=2000;

   if (nbsolvers < 8 ) return; 

   ms->solvers[7]->var_decay = 0.94;
   ms->solvers[7]->max_var_decay = 0.96;
   ms->solvers[7]->firstReduceDB=800;

   if (nbsolvers < 9) return;

//   ms->solvers[8]->reduceOnSize = true; // NOT USED ANYMORE

   if (nbsolvers < 10 ) return;

//   ms->solvers[9]->reduceOnSize = true; // NOT USED ANYMORE
//   ms->solvers[9]->reduceOnSizeSize = 14;

   if (nbsolvers < 11 ) return;

   double noisevar_decay = 0.005;
   int noiseReduceDB = 50;
   for (int i=10;i<nbsolvers;i++) {
       ms->solvers[i]-> var_decay = ms->solvers[i%8]->var_decay;
       ms->solvers[i]-> max_var_decay = ms->solvers[i%8]->max_var_decay;
       ms->solvers[i]-> firstReduceDB= ms->solvers[i%8]->firstReduceDB;
       ms->solvers[i]->var_decay += noisevar_decay;
       ms->solvers[i]->firstReduceDB+=noiseReduceDB;
       if ((i+1) % 8 == 0) {
	   noisevar_decay += 0.006;
	   noiseReduceDB += 25;
       }
   }
 }
