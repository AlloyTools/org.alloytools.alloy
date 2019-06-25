/***************************************************************************************[Main.cc]
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

#include <errno.h>

#include <signal.h>
#include <zlib.h>


#include "utils/System.h"
#include "utils/ParseUtils.h"
#include "utils/Options.h"
#include "core/Dimacs.h"
#include "core/SolverTypes.h"

#include "simp/SimpSolver.h"
#include "parallel/ParallelSolver.h"
#include "parallel/MultiSolvers.h"

using namespace Glucose;



static MultiSolvers* pmsolver;

// Terminate by notifying the solver and back out gracefully. This is mainly to have a test-case
// for this feature of the Solver as it may take longer than an immediate call to '_exit()'.
//static void SIGINT_interrupt(int signum) { pmsolver->interrupt(); }


// Note that '_exit()' rather than 'exit()' has to be used. The reason is that 'exit()' calls
// destructors and may cause deadlocks if a malloc/free function happens to be running (these
// functions are guarded by locks for multithreaded use).
static void SIGINT_exit(int signum) {
    printf("\n"); printf("*** INTERRUPTED ***\n");
    if (pmsolver->verbosity() > 0){
        pmsolver->printFinalStats();
        printf("\n"); printf("*** INTERRUPTED ***\n"); }
    _exit(1); }


//=================================================================================================
// Main:


int main(int argc, char** argv)
{
    double realTimeStart = realTime();
  printf("c\nc This is glucose-syrup 4.0 (glucose in many threads) --  based on MiniSAT (Many thanks to MiniSAT team)\nc\n");
    try {
        setUsageHelp("c USAGE: %s [options] <input-file> <result-output-file>\n\n  where input may be either in plain or gzipped DIMACS.\n");
        // printf("This is MiniSat 2.0 beta\n");
        
#if defined(__linux__)
        fpu_control_t oldcw, newcw;
        _FPU_GETCW(oldcw); newcw = (oldcw & ~_FPU_EXTENDED) | _FPU_DOUBLE; _FPU_SETCW(newcw);
        printf("c WARNING: for repeatability, setting FPU to use double precision\n");
#endif
        // Extra options:
        //
        IntOption    verb   ("MAIN", "verb",   "Verbosity level (0=silent, 1=some, 2=more).", 1, IntRange(0, 2));
        BoolOption   mod   ("MAIN", "model",   "show model.", false);
        IntOption    vv  ("MAIN", "vv",   "Verbosity every vv conflicts", 10000, IntRange(1,INT32_MAX));
        BoolOption   pre    ("MAIN", "pre",    "Completely turn on/off any preprocessing.", true);

        IntOption    cpu_lim("MAIN", "cpu-lim","Limit on CPU time allowed in seconds.\n", INT32_MAX, IntRange(0, INT32_MAX));
        IntOption    mem_lim("MAIN", "mem-lim","Limit on memory usage in megabytes.\n", INT32_MAX, IntRange(0, INT32_MAX));
        
        parseOptions(argc, argv, true);

	MultiSolvers msolver;
        pmsolver = & msolver;
        msolver.setVerbosity(verb);
        msolver.setVerbEveryConflicts(vv);
        msolver.setShowModel(mod);

        double initial_time = cpuTime();

	        // Use signal handlers that forcibly quit until the solver will be able to respond to
        // interrupts:
	signal(SIGINT, SIGINT_exit);
        signal(SIGXCPU,SIGINT_exit);

        // Set limit on CPU-time:
        if (cpu_lim != INT32_MAX){
            rlimit rl;
            getrlimit(RLIMIT_CPU, &rl);
            if (rl.rlim_max == RLIM_INFINITY || (rlim_t)cpu_lim < rl.rlim_max){
                rl.rlim_cur = cpu_lim;
                if (setrlimit(RLIMIT_CPU, &rl) == -1)
                    printf("c WARNING! Could not set resource limit: CPU-time.\n");
            } }

        // Set limit on virtual memory:
        if (mem_lim != INT32_MAX){
            rlim_t new_mem_lim = (rlim_t)mem_lim * 1024*1024;
            rlimit rl;
            getrlimit(RLIMIT_AS, &rl);
            if (rl.rlim_max == RLIM_INFINITY || new_mem_lim < rl.rlim_max){
                rl.rlim_cur = new_mem_lim;
                if (setrlimit(RLIMIT_AS, &rl) == -1)
                    printf("c WARNING! Could not set resource limit: Virtual memory.\n");
            } }
        
        if (argc == 1)
            printf("c Reading from standard input... Use '--help' for help.\n");
        
        gzFile in = (argc == 1) ? gzdopen(0, "rb") : gzopen(argv[1], "rb");
        if (in == NULL)
            printf("c ERROR! Could not open file: %s\n", argc == 1 ? "<stdin>" : argv[1]), exit(1);
        
        if (msolver.verbosity() > 0){
            printf("c ========================================[ Problem Statistics ]===========================================\n");
            printf("c |                                                                                                       |\n"); }
        
        parse_DIMACS(in, msolver);
        gzclose(in);
        

	
        FILE* res = (argc >= 3) ? fopen(argv[argc-1], "wb") : NULL;

        if (msolver.verbosity() > 0){
            printf("c |  Number of variables:  %12d                                                                   |\n", msolver.nVars());
            printf("c |  Number of clauses:    %12d                                                                   |\n", msolver.nClauses()); }
        
        double parsed_time = cpuTime();
        if (msolver.verbosity() > 0){
            printf("c |  Parse time:           %12.2f s                                                                 |\n", parsed_time - initial_time);
            printf("c |                                                                                                       |\n"); }
 
        // Change to signal-handlers that will only notify the solver and allow it to terminate
        // voluntarily:
        //signal(SIGINT, SIGINT_interrupt);
        //signal(SIGXCPU,SIGINT_interrupt);
 
        
	int ret2 = msolver.simplify();   
        msolver.use_simplification = pre; 	
        if(ret2) 
            msolver.eliminate();
        if(pre) {
            double simplified_time = cpuTime();
            if (msolver.verbosity() > 0){
                printf("c |  Simplification time:  %12.2f s                                                                 |\n", simplified_time - parsed_time);
                printf("c |                                                                                                       |\n"); }
        }
        
        if (!ret2 || !msolver.okay()){
            //if (S.certifiedOutput != NULL) fprintf(S.certifiedOutput, "0\n"), fclose(S.certifiedOutput);
            if (res != NULL) fprintf(res, "UNSAT\n"), fclose(res);
            if (msolver.verbosity() > 0){
	        printf("c =========================================================================================================\n");
                printf("Solved by unit propagation\n"); 
		printf("c real time : %g s\n", realTime() - realTimeStart);
		printf("c cpu time  : %g s\n", cpuTime());
                printf("\n"); }
            printf("s UNSATISFIABLE\n");
            exit(20);
        }

      //  vec<Lit> dummy;
        lbool ret = msolver.solve();
	
	
        printf("c\n");
    	printf("c real time : %g s\n", realTime() - realTimeStart);
	printf("c cpu time  : %g s\n", cpuTime());
        if (msolver.verbosity() > 0){
            msolver.printFinalStats();
            printf("\n"); }

	//-------------- Result is put in a external file
     	/* I must admit I have to print the model of one thread... But which one? FIXME !!
	  if (res != NULL){  
	  if (ret == l_True){
	    fprintf(res, "SAT\n");
	    for (int i = 0; i < S.nVars(); i++)
	      if (S.model[i] != l_Undef)
		fprintf(res, "%s%s%d", (i==0)?"":" ", (S.model[i]==l_True)?"":"-", i+1);
	    fprintf(res, " 0\n");
	  }else if (ret == l_False)
	    fprintf(res, "UNSAT\n");
	  else
	    fprintf(res, "INDET\n");
	  fclose(res);
	
	//-------------- Want certified output
        } else { 
	*/
	  printf(ret == l_True ? "s SATISFIABLE\n" : ret == l_False ? "s UNSATISFIABLE\n" : "s INDETERMINATE\n");
	  
	  if(msolver.getShowModel() && ret==l_True) {
	    printf("v ");
	    for (int i = 0; i < msolver.model.size() ; i++) {
                assert(msolver.model[i] != l_Undef);
                if (msolver.model[i] != l_Undef)
		printf("%s%s%d", (i==0)?"":" ", (msolver.model[i]==l_True)?"":"-", i+1);
            }
	    printf(" 0\n");
	  }

     
    
#ifdef NDEBUG
        exit(ret == l_True ? 10 : ret == l_False ? 20 : 0);     // (faster than "return", which will invoke the destructor for 'Solver')
#else
        return (ret == l_True ? 10 : ret == l_False ? 20 : 0);
#endif
    } catch (OutOfMemoryException&){
      printf("c ===================================================================================================\n");
        printf("INDETERMINATE\n");
        exit(0);
    }
}
