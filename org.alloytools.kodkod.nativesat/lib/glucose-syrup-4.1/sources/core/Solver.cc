/***************************************************************************************[Solver.cc]
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

#include <math.h>

#include "utils/System.h"
#include "mtl/Sort.h"
#include "core/Solver.h"
#include "core/Constants.h"
#include"simp/SimpSolver.h"

using namespace Glucose;


//=================================================================================================
// Statistics
//=================================================================================================



//=================================================================================================
// Options:

static const char *_cat = "CORE";
static const char *_cr = "CORE -- RESTART";
static const char *_cred = "CORE -- REDUCE";
static const char *_cm = "CORE -- MINIMIZE";


static DoubleOption opt_K(_cr, "K", "The constant used to force restart", 0.8, DoubleRange(0, false, 1, false));
static DoubleOption opt_R(_cr, "R", "The constant used to block restart", 1.4, DoubleRange(1, false, 5, false));
static IntOption opt_size_lbd_queue(_cr, "szLBDQueue", "The size of moving average for LBD (restarts)", 50, IntRange(10, INT32_MAX));
static IntOption opt_size_trail_queue(_cr, "szTrailQueue", "The size of moving average for trail (block restarts)", 5000, IntRange(10, INT32_MAX));

static IntOption opt_first_reduce_db(_cred, "firstReduceDB", "The number of conflicts before the first reduce DB (or the size of leernts if chanseok is used)",
                                     2000, IntRange(0, INT32_MAX));
static IntOption opt_inc_reduce_db(_cred, "incReduceDB", "Increment for reduce DB", 300, IntRange(0, INT32_MAX));
static IntOption opt_spec_inc_reduce_db(_cred, "specialIncReduceDB", "Special increment for reduce DB", 1000, IntRange(0, INT32_MAX));
static IntOption opt_lb_lbd_frozen_clause(_cred, "minLBDFrozenClause", "Protect clauses if their LBD decrease and is lower than (for one turn)", 30,
                                          IntRange(0, INT32_MAX));
static BoolOption opt_chanseok_hack(_cred, "chanseok",
                                    "Use Chanseok Oh strategy for LBD (keep all LBD<=co and remove half of firstreduceDB other learnt clauses", false);
static IntOption opt_chanseok_limit(_cred, "co", "Chanseok Oh: all learnt clauses with LBD<=co are permanent", 5, IntRange(2, INT32_MAX));


static IntOption opt_lb_size_minimzing_clause(_cm, "minSizeMinimizingClause", "The min size required to minimize clause", 30, IntRange(3, INT32_MAX));
static IntOption opt_lb_lbd_minimzing_clause(_cm, "minLBDMinimizingClause", "The min LBD required to minimize clause", 6, IntRange(3, INT32_MAX));


static DoubleOption opt_var_decay(_cat, "var-decay", "The variable activity decay factor (starting point)", 0.8, DoubleRange(0, false, 1, false));
static DoubleOption opt_max_var_decay(_cat, "max-var-decay", "The variable activity decay factor", 0.95, DoubleRange(0, false, 1, false));
static DoubleOption opt_clause_decay(_cat, "cla-decay", "The clause activity decay factor", 0.999, DoubleRange(0, false, 1, false));
static DoubleOption opt_random_var_freq(_cat, "rnd-freq", "The frequency with which the decision heuristic tries to choose a random variable", 0,
                                        DoubleRange(0, true, 1, true));
static DoubleOption opt_random_seed(_cat, "rnd-seed", "Used by the random variable selection", 91648253, DoubleRange(0, false, HUGE_VAL, false));
static IntOption opt_ccmin_mode(_cat, "ccmin-mode", "Controls conflict clause minimization (0=none, 1=basic, 2=deep)", 2, IntRange(0, 2));
static IntOption opt_phase_saving(_cat, "phase-saving", "Controls the level of phase saving (0=none, 1=limited, 2=full)", 2, IntRange(0, 2));
static BoolOption opt_rnd_init_act(_cat, "rnd-init", "Randomize the initial activity", false);
static DoubleOption opt_garbage_frac(_cat, "gc-frac", "The fraction of wasted memory allowed before a garbage collection is triggered", 0.20,
                                     DoubleRange(0, false, HUGE_VAL, false));
static BoolOption opt_glu_reduction(_cat, "gr", "glucose strategy to fire clause database reduction (must be false to fire Chanseok strategy)", true);
static BoolOption opt_luby_restart(_cat, "luby", "Use the Luby restart sequence", false);
static DoubleOption opt_restart_inc(_cat, "rinc", "Restart interval increase factor", 2, DoubleRange(1, false, HUGE_VAL, false));
static IntOption opt_luby_restart_factor(_cred, "luby-factor", "Luby restart factor", 100, IntRange(1, INT32_MAX));

static IntOption opt_randomize_phase_on_restarts(_cat, "phase-restart",
                                                 "The amount of randomization for the phase at each restart (0=none, 1=first branch, 2=first branch (no bad clauses), 3=first branch (only initial clauses)",
                                                 0, IntRange(0, 3));
static BoolOption opt_fixed_randomize_phase_on_restarts(_cat, "fix-phas-rest", "Fixes the first 7 levels at random phase", false);

static BoolOption opt_adapt(_cat, "adapt", "Adapt dynamically stategies after 100000 conflicts", true);

static BoolOption opt_forceunsat(_cat,"forceunsat","Force the phase for UNSAT",true);
//=================================================================================================
// Constructor/Destructor:

Solver::Solver() :

// Parameters (user settable):
//
verbosity(0)
, showModel(0)
, K(opt_K)
, R(opt_R)
, sizeLBDQueue(opt_size_lbd_queue)
, sizeTrailQueue(opt_size_trail_queue)
, firstReduceDB(opt_first_reduce_db)
, incReduceDB(opt_chanseok_hack ? 0 : opt_inc_reduce_db)
, specialIncReduceDB(opt_chanseok_hack ? 0 : opt_spec_inc_reduce_db)
, lbLBDFrozenClause(opt_lb_lbd_frozen_clause)
, chanseokStrategy(opt_chanseok_hack)
, coLBDBound (opt_chanseok_limit)
, lbSizeMinimizingClause(opt_lb_size_minimzing_clause)
, lbLBDMinimizingClause(opt_lb_lbd_minimzing_clause)
, var_decay(opt_var_decay)
, max_var_decay(opt_max_var_decay)
, clause_decay(opt_clause_decay)
, random_var_freq(opt_random_var_freq)
, random_seed(opt_random_seed)
, ccmin_mode(opt_ccmin_mode)
, phase_saving(opt_phase_saving)
, rnd_pol(false)
, rnd_init_act(opt_rnd_init_act)
, randomizeFirstDescent(false)
, garbage_frac(opt_garbage_frac)
, certifiedOutput(NULL)
, certifiedUNSAT(false) // Not in the first parallel version
, vbyte(false)
, panicModeLastRemoved(0), panicModeLastRemovedShared(0)
, useUnaryWatched(false)
, promoteOneWatchedClause(true)
,solves(0),starts(0),decisions(0),propagations(0),conflicts(0),conflictsRestarts(0)
, curRestart(1)
, glureduce(opt_glu_reduction)
, restart_inc(opt_restart_inc)
, luby_restart(opt_luby_restart)
, adaptStrategies(opt_adapt)
, luby_restart_factor(opt_luby_restart_factor)
, randomize_on_restarts(opt_randomize_phase_on_restarts)
, fixed_randomize_on_restarts(opt_fixed_randomize_phase_on_restarts)
, newDescent(0)
, randomDescentAssignments(0)
, forceUnsatOnNewDescent(opt_forceunsat)

, ok(true)
, cla_inc(1)
, var_inc(1)
, watches(WatcherDeleted(ca))
, watchesBin(WatcherDeleted(ca))
, unaryWatches(WatcherDeleted(ca))
, qhead(0)
, simpDB_assigns(-1)
, simpDB_props(0)
, order_heap(VarOrderLt(activity))
, progress_estimate(0)
, remove_satisfied(true)
,lastLearntClause(CRef_Undef)
// Resource constraints:
//
, conflict_budget(-1)
, propagation_budget(-1)
, asynch_interrupt(false)
, incremental(false)
, nbVarsInitialFormula(INT32_MAX)
, totalTime4Sat(0.)
, totalTime4Unsat(0.)
, nbSatCalls(0)
, nbUnsatCalls(0)
{
    MYFLAG = 0;
    // Initialize only first time. Useful for incremental solving (not in // version), useless otherwise
    // Kept here for simplicity
    lbdQueue.initSize(sizeLBDQueue);
    trailQueue.initSize(sizeTrailQueue);
    sumLBD = 0;
    nbclausesbeforereduce = firstReduceDB;
    stats.growTo(coreStatsSize, 0);
}

//-------------------------------------------------------
// Special constructor used for cloning solvers
//-------------------------------------------------------

Solver::Solver(const Solver &s) :
  verbosity(s.verbosity)
, showModel(s.showModel)
, K(s.K)
, R(s.R)
, sizeLBDQueue(s.sizeLBDQueue)
, sizeTrailQueue(s.sizeTrailQueue)
, firstReduceDB(s.firstReduceDB)
, incReduceDB(s.incReduceDB)
, specialIncReduceDB(s.specialIncReduceDB)
, lbLBDFrozenClause(s.lbLBDFrozenClause)
, chanseokStrategy(opt_chanseok_hack)
, coLBDBound (opt_chanseok_limit)
, lbSizeMinimizingClause(s.lbSizeMinimizingClause)
, lbLBDMinimizingClause(s.lbLBDMinimizingClause)
, var_decay(s.var_decay)
, max_var_decay(s.max_var_decay)
, clause_decay(s.clause_decay)
, random_var_freq(s.random_var_freq)
, random_seed(s.random_seed)
, ccmin_mode(s.ccmin_mode)
, phase_saving(s.phase_saving)
, rnd_pol(s.rnd_pol)
, rnd_init_act(s.rnd_init_act)
, randomizeFirstDescent(s.randomizeFirstDescent)
, garbage_frac(s.garbage_frac)
, certifiedOutput(NULL)
, certifiedUNSAT(false) // Not in the first parallel version
, panicModeLastRemoved(s.panicModeLastRemoved), panicModeLastRemovedShared(s.panicModeLastRemovedShared)
, useUnaryWatched(s.useUnaryWatched)
, promoteOneWatchedClause(s.promoteOneWatchedClause)
// Statistics: (formerly in 'SolverStats')
//
,solves(0),starts(0),decisions(0),propagations(0),conflicts(0),conflictsRestarts(0)

, curRestart(s.curRestart)
, glureduce(s.glureduce)
, restart_inc(s.restart_inc)
, luby_restart(s.luby_restart)
, adaptStrategies(s.adaptStrategies)
, luby_restart_factor(s.luby_restart_factor)
, randomize_on_restarts(s.randomize_on_restarts)
, fixed_randomize_on_restarts(s.fixed_randomize_on_restarts)
, newDescent(s.newDescent)
, randomDescentAssignments(s.randomDescentAssignments)
, forceUnsatOnNewDescent(s.forceUnsatOnNewDescent)
, ok(true)
, cla_inc(s.cla_inc)
, var_inc(s.var_inc)
, watches(WatcherDeleted(ca))
, watchesBin(WatcherDeleted(ca))
, unaryWatches(WatcherDeleted(ca))
, qhead(s.qhead)
, simpDB_assigns(s.simpDB_assigns)
, simpDB_props(s.simpDB_props)
, order_heap(VarOrderLt(activity))
, progress_estimate(s.progress_estimate)
, remove_satisfied(s.remove_satisfied)
,lastLearntClause(CRef_Undef)
// Resource constraints:
//
, conflict_budget(s.conflict_budget)
, propagation_budget(s.propagation_budget)
, asynch_interrupt(s.asynch_interrupt)
, incremental(s.incremental)
, nbVarsInitialFormula(s.nbVarsInitialFormula)
, totalTime4Sat(s.totalTime4Sat)
, totalTime4Unsat(s.totalTime4Unsat)
, nbSatCalls(s.nbSatCalls)
, nbUnsatCalls(s.nbUnsatCalls)
{
    // Copy clauses.
    s.ca.copyTo(ca);
    ca.extra_clause_field = s.ca.extra_clause_field;

    // Initialize  other variables
    MYFLAG = 0;
    // Initialize only first time. Useful for incremental solving (not in // version), useless otherwise
    // Kept here for simplicity
    sumLBD = s.sumLBD;
    nbclausesbeforereduce = s.nbclausesbeforereduce;

    // Copy all search vectors
    s.watches.copyTo(watches);
    s.watchesBin.copyTo(watchesBin);
    s.unaryWatches.copyTo(unaryWatches);
    s.assigns.memCopyTo(assigns);
    s.vardata.memCopyTo(vardata);
    s.activity.memCopyTo(activity);
    s.seen.memCopyTo(seen);
    s.permDiff.memCopyTo(permDiff);
    s.polarity.memCopyTo(polarity);
    s.decision.memCopyTo(decision);
    s.trail.memCopyTo(trail);
    s.order_heap.copyTo(order_heap);
    s.clauses.memCopyTo(clauses);
    s.learnts.memCopyTo(learnts);
    s.permanentLearnts.memCopyTo(permanentLearnts);

    s.lbdQueue.copyTo(lbdQueue);
    s.trailQueue.copyTo(trailQueue);
    s.forceUNSAT.copyTo(forceUNSAT);
    s.stats.copyTo(stats);
}


Solver::~Solver() {
}


/****************************************************************
 Certified UNSAT proof in binary format
****************************************************************/


void Solver::write_char(unsigned char ch) {
    if(putc_unlocked((int) ch, certifiedOutput) == EOF)
        exit(1);
}


void Solver::write_lit(int n) {
    for(; n > 127; n >>= 7)
        write_char(128 | (n & 127));
    write_char(n);
}

/****************************************************************
 Set the incremental mode
****************************************************************/

// This function set the incremental mode to true.
// You can add special code for this mode here.

void Solver::setIncrementalMode() {
#ifdef INCREMENTAL
    incremental = true;
#else
    fprintf(stderr, "c Trying to set incremental mode, but not compiled properly for this.\n");
    exit(1);
#endif
}


// Number of variables without selectors
void Solver::initNbInitialVars(int nb) {
    nbVarsInitialFormula = nb;
}


bool Solver::isIncremental() {
    return incremental;
}


//=================================================================================================
// Minor methods:


// Creates a new SAT variable in the solver. If 'decision' is cleared, variable will not be
// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
//

Var Solver::newVar(bool sign, bool dvar) {
    int v = nVars();
    watches.init(mkLit(v, false));
    watches.init(mkLit(v, true));
    watchesBin.init(mkLit(v, false));
    watchesBin.init(mkLit(v, true));
    unaryWatches.init(mkLit(v, false));
    unaryWatches.init(mkLit(v, true));
    assigns.push(l_Undef);
    vardata.push(mkVarData(CRef_Undef, 0));
    activity.push(rnd_init_act ? drand(random_seed) * 0.00001 : 0);
    seen.push(0);
    permDiff.push(0);
    polarity.push(sign);
    forceUNSAT.push(0);
    decision.push();
    trail.capacity(v + 1);
    setDecisionVar(v, dvar);
    return v;
}


bool Solver::addClause_(vec <Lit> &ps) {

    assert(decisionLevel() == 0);
    if(!ok) return false;

    // Check if clause is satisfied and remove false/duplicate literals:
    sort(ps);

    vec <Lit> oc;
    oc.clear();

    Lit p;
    int i, j, flag = 0;
    if(certifiedUNSAT) {
        for(i = j = 0, p = lit_Undef; i < ps.size(); i++) {
            oc.push(ps[i]);
            if(value(ps[i]) == l_True || ps[i] == ~p || value(ps[i]) == l_False)
                flag = 1;
        }
    }

    for(i = j = 0, p = lit_Undef; i < ps.size(); i++)
        if(value(ps[i]) == l_True || ps[i] == ~p)
            return true;
        else if(value(ps[i]) != l_False && ps[i] != p)
            ps[j++] = p = ps[i];
    ps.shrink(i - j);

    if(flag && (certifiedUNSAT)) {
        if(vbyte) {
            write_char('a');
            for(i = j = 0, p = lit_Undef; i < ps.size(); i++)
                write_lit(2 * (var(ps[i]) + 1) + sign(ps[i]));
            write_lit(0);

            write_char('d');
            for(i = j = 0, p = lit_Undef; i < oc.size(); i++)
                write_lit(2 * (var(oc[i]) + 1) + sign(oc[i]));
            write_lit(0);
        }
        else {
            for(i = j = 0, p = lit_Undef; i < ps.size(); i++)
                fprintf(certifiedOutput, "%i ", (var(ps[i]) + 1) * (-2 * sign(ps[i]) + 1));
            fprintf(certifiedOutput, "0\n");

            fprintf(certifiedOutput, "d ");
            for(i = j = 0, p = lit_Undef; i < oc.size(); i++)
                fprintf(certifiedOutput, "%i ", (var(oc[i]) + 1) * (-2 * sign(oc[i]) + 1));
            fprintf(certifiedOutput, "0\n");
        }
    }


    if(ps.size() == 0)
        return ok = false;
    else if(ps.size() == 1) {
        uncheckedEnqueue(ps[0]);
        return ok = (propagate() == CRef_Undef);
    } else {
        CRef cr = ca.alloc(ps, false);
        clauses.push(cr);
        attachClause(cr);
    }

    return true;
}


void Solver::attachClause(CRef cr) {
    const Clause &c = ca[cr];

    assert(c.size() > 1);
    if(c.size() == 2) {
        watchesBin[~c[0]].push(Watcher(cr, c[1]));
        watchesBin[~c[1]].push(Watcher(cr, c[0]));
    } else {
        watches[~c[0]].push(Watcher(cr, c[1]));
        watches[~c[1]].push(Watcher(cr, c[0]));
    }
    if(c.learnt()) stats[learnts_literals] += c.size();
    else stats[clauses_literals] += c.size();
}


void Solver::attachClausePurgatory(CRef cr) {
    const Clause &c = ca[cr];

    assert(c.size() > 1);
    unaryWatches[~c[0]].push(Watcher(cr, c[1]));

}


void Solver::detachClause(CRef cr, bool strict) {
    const Clause &c = ca[cr];

    assert(c.size() > 1);
    if(c.size() == 2) {
        if(strict) {
            remove(watchesBin[~c[0]], Watcher(cr, c[1]));
            remove(watchesBin[~c[1]], Watcher(cr, c[0]));
        } else {
            // Lazy detaching: (NOTE! Must clean all watcher lists before garbage collecting this clause)
            watchesBin.smudge(~c[0]);
            watchesBin.smudge(~c[1]);
        }
    } else {
        if(strict) {
            remove(watches[~c[0]], Watcher(cr, c[1]));
            remove(watches[~c[1]], Watcher(cr, c[0]));
        } else {
            // Lazy detaching: (NOTE! Must clean all watcher lists before garbage collecting this clause)
            watches.smudge(~c[0]);
            watches.smudge(~c[1]);
        }
    }
    if(c.learnt()) stats[learnts_literals] -= c.size();
    else stats[clauses_literals] -= c.size();
}


// The purgatory is the 1-Watched scheme for imported clauses

void Solver::detachClausePurgatory(CRef cr, bool strict) {
    const Clause &c = ca[cr];

    assert(c.size() > 1);
    if(strict)
        remove(unaryWatches[~c[0]], Watcher(cr, c[1]));
    else
        unaryWatches.smudge(~c[0]);
}


void Solver::removeClause(CRef cr, bool inPurgatory) {

    Clause &c = ca[cr];

    if(certifiedUNSAT) {
        if(vbyte) {
            write_char('d');
            for(int i = 0; i < c.size(); i++)
                write_lit(2 * (var(c[i]) + 1) + sign(c[i]));
            write_lit(0);
        }
        else {
            fprintf(certifiedOutput, "d ");
            for(int i = 0; i < c.size(); i++)
                fprintf(certifiedOutput, "%i ", (var(c[i]) + 1) * (-2 * sign(c[i]) + 1));
            fprintf(certifiedOutput, "0\n");
        }
    }

    if(inPurgatory)
        detachClausePurgatory(cr);
    else
        detachClause(cr);
    // Don't leave pointers to free'd memory!
    if(locked(c)) vardata[var(c[0])].reason = CRef_Undef;
    c.mark(1);
    ca.free(cr);
}


bool Solver::satisfied(const Clause &c) const {
#ifdef INCREMENTAL
    if(incremental)
        return (value(c[0]) == l_True) || (value(c[1]) == l_True);
#endif

    // Default mode
    for(int i = 0; i < c.size(); i++)
        if(value(c[i]) == l_True)
            return true;
    return false;
}


/************************************************************
 * Compute LBD functions
 *************************************************************/

template <typename T>inline unsigned int Solver::computeLBD(const T &lits, int end) {
    int nblevels = 0;
    MYFLAG++;
#ifdef INCREMENTAL
    if(incremental) { // ----------------- INCREMENTAL MODE
      if(end==-1) end = lits.size();
      int nbDone = 0;
      for(int i=0;i<lits.size();i++) {
        if(nbDone>=end) break;
        if(isSelector(var(lits[i]))) continue;
        nbDone++;
        int l = level(var(lits[i]));
        if (permDiff[l] != MYFLAG) {
      permDiff[l] = MYFLAG;
      nblevels++;
        }
      }
    } else { // -------- DEFAULT MODE. NOT A LOT OF DIFFERENCES... BUT EASIER TO READ
#endif
    for(int i = 0; i < lits.size(); i++) {
        int l = level(var(lits[i]));
        if(permDiff[l] != MYFLAG) {
            permDiff[l] = MYFLAG;
            nblevels++;
        }
    }
#ifdef INCREMENTAL
    }
#endif
    return nblevels;
}



/******************************************************************
 * Minimisation with binary reolution
 ******************************************************************/
void Solver::minimisationWithBinaryResolution(vec <Lit> &out_learnt) {

    // Find the LBD measure
    unsigned int lbd = computeLBD(out_learnt);
    Lit p = ~out_learnt[0];

    if(lbd <= lbLBDMinimizingClause) {
        MYFLAG++;

        for(int i = 1; i < out_learnt.size(); i++) {
            permDiff[var(out_learnt[i])] = MYFLAG;
        }

        vec <Watcher> &wbin = watchesBin[p];
        int nb = 0;
        for(int k = 0; k < wbin.size(); k++) {
            Lit imp = wbin[k].blocker;
            if(permDiff[var(imp)] == MYFLAG && value(imp) == l_True) {
                nb++;
                permDiff[var(imp)] = MYFLAG - 1;
            }
        }
        int l = out_learnt.size() - 1;
        if(nb > 0) {
            stats[nbReducedClauses]++;
            for(int i = 1; i < out_learnt.size() - nb; i++) {
                if(permDiff[var(out_learnt[i])] != MYFLAG) {
                    Lit p = out_learnt[l];
                    out_learnt[l] = out_learnt[i];
                    out_learnt[i] = p;
                    l--;
                    i--;
                }
            }

            out_learnt.shrink(nb);

        }
    }
}

// Revert to the state at given level (keeping all assignment at 'level' but not beyond).
//

void Solver::cancelUntil(int level) {
    if(decisionLevel() > level) {
        for(int c = trail.size() - 1; c >= trail_lim[level]; c--) {
            Var x = var(trail[c]);
            assigns[x] = l_Undef;
            if(phase_saving > 1 || ((phase_saving == 1) && c > trail_lim.last())) {
                polarity[x] = sign(trail[c]);
            }
            insertVarOrder(x);
        }
        qhead = trail_lim[level];
        trail.shrink(trail.size() - trail_lim[level]);
        trail_lim.shrink(trail_lim.size() - level);
    }
}


//=================================================================================================
// Major methods:

Lit Solver::pickBranchLit() {
    Var next = var_Undef;

    // Random decision:
    if(((randomizeFirstDescent && conflicts == 0) || drand(random_seed) < random_var_freq) && !order_heap.empty()) {
        next = order_heap[irand(random_seed, order_heap.size())];
        if(value(next) == l_Undef && decision[next])
            stats[rnd_decisions]++;
    }

    // Activity based decision:
    while(next == var_Undef || value(next) != l_Undef || !decision[next])
        if(order_heap.empty()) {
            next = var_Undef;
            break;
        } else {
            next = order_heap.removeMin();
        }

    if(randomize_on_restarts && !fixed_randomize_on_restarts && newDescent && (decisionLevel() % 2 == 0)) {
        return mkLit(next, (randomDescentAssignments >> (decisionLevel() % 32)) & 1);
    }

    if(fixed_randomize_on_restarts && decisionLevel() < 7) {
        return mkLit(next, (randomDescentAssignments >> (decisionLevel() % 32)) & 1);
    }

    if(next == var_Undef) return lit_Undef;

    if(forceUnsatOnNewDescent && newDescent) {
        if(forceUNSAT[next] != 0)
            return mkLit(next, forceUNSAT[next] < 0);
        return mkLit(next, polarity[next]);

    }

    return next == var_Undef ? lit_Undef : mkLit(next, rnd_pol ? drand(random_seed) < 0.5 : polarity[next]);
}


/*_________________________________________________________________________________________________
|
|  analyze : (confl : Clause*) (out_learnt : vec<Lit>&) (out_btlevel : int&)  ->  [void]
|  
|  Description:
|    Analyze conflict and produce a reason clause.
|  
|    Pre-conditions:
|      * 'out_learnt' is assumed to be cleared.
|      * Current decision level must be greater than root level.
|  
|    Post-conditions:
|      * 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.
|      * If out_learnt.size() > 1 then 'out_learnt[1]' has the greatest decision level of the 
|        rest of literals. There may be others from the same level though.
|  
|________________________________________________________________________________________________@*/
void Solver::analyze(CRef confl, vec <Lit> &out_learnt, vec <Lit> &selectors, int &out_btlevel, unsigned int &lbd, unsigned int &szWithoutSelectors) {
    int pathC = 0;
    Lit p = lit_Undef;


    // Generate conflict clause:
    //
    out_learnt.push(); // (leave room for the asserting literal)
    int index = trail.size() - 1;
    do {
        assert(confl != CRef_Undef); // (otherwise should be UIP)
        Clause &c = ca[confl];
        // Special case for binary clauses
        // The first one has to be SAT
        if(p != lit_Undef && c.size() == 2 && value(c[0]) == l_False) {

            assert(value(c[1]) == l_True);
            Lit tmp = c[0];
            c[0] = c[1], c[1] = tmp;
        }

        if(c.learnt()) {
            parallelImportClauseDuringConflictAnalysis(c, confl);
            claBumpActivity(c);
        } else { // original clause
            if(!c.getSeen()) {
                stats[originalClausesSeen]++;
                c.setSeen(true);
            }
        }

        // DYNAMIC NBLEVEL trick (see competition'09 companion paper)
        if(c.learnt() && c.lbd() > 2) {
            unsigned int nblevels = computeLBD(c);
            if(nblevels + 1 < c.lbd()) { // improve the LBD
                if(c.lbd() <= lbLBDFrozenClause) {
                    // seems to be interesting : keep it for the next round
                    c.setCanBeDel(false);
                }
                if(chanseokStrategy && nblevels <= coLBDBound) {
                    c.nolearnt();
                    learnts.remove(confl);
                    permanentLearnts.push(confl);
                    stats[nbPermanentLearnts]++;

                } else {
                    c.setLBD(nblevels); // Update it
                }
            }
        }


        for(int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++) {
            Lit q = c[j];

            if(!seen[var(q)]) {
                if(level(var(q)) == 0) {
                } else { // Here, the old case
                    if(!isSelector(var(q)))
                        varBumpActivity(var(q));

                    // This variable was responsible for a conflict,
                    // consider it as a UNSAT assignation for this literal
                    bumpForceUNSAT(~q); // Negation because q is false here

                    seen[var(q)] = 1;
                    if(level(var(q)) >= decisionLevel()) {
                        pathC++;
                        // UPDATEVARACTIVITY trick (see competition'09 companion paper)
                        if(!isSelector(var(q)) && (reason(var(q)) != CRef_Undef) && ca[reason(var(q))].learnt())
                            lastDecisionLevel.push(q);
                    } else {
                        if(isSelector(var(q))) {
                            assert(value(q) == l_False);
                            selectors.push(q);
                        } else
                            out_learnt.push(q);
                    }
                }
            } //else stats[sumResSeen]++;
        }

        // Select next clause to look at:
        while (!seen[var(trail[index--])]);
        p = trail[index + 1];
        //stats[sumRes]++;
        confl = reason(var(p));
        seen[var(p)] = 0;
        pathC--;

    } while(pathC > 0);
    out_learnt[0] = ~p;

    // Simplify conflict clause:
    //
    int i, j;

    for(int i = 0; i < selectors.size(); i++)
        out_learnt.push(selectors[i]);

    out_learnt.copyTo(analyze_toclear);
    if(ccmin_mode == 2) {
        uint32_t abstract_level = 0;
        for(i = 1; i < out_learnt.size(); i++)
            abstract_level |= abstractLevel(var(out_learnt[i])); // (maintain an abstraction of levels involved in conflict)

        for(i = j = 1; i < out_learnt.size(); i++)
            if(reason(var(out_learnt[i])) == CRef_Undef || !litRedundant(out_learnt[i], abstract_level))
                out_learnt[j++] = out_learnt[i];

    } else if(ccmin_mode == 1) {
        for(i = j = 1; i < out_learnt.size(); i++) {
            Var x = var(out_learnt[i]);

            if(reason(x) == CRef_Undef)
                out_learnt[j++] = out_learnt[i];
            else {
                Clause &c = ca[reason(var(out_learnt[i]))];
                // Thanks to Siert Wieringa for this bug fix!
                for(int k = ((c.size() == 2) ? 0 : 1); k < c.size(); k++)
                    if(!seen[var(c[k])] && level(var(c[k])) > 0) {
                        out_learnt[j++] = out_learnt[i];
                        break;
                    }
            }
        }
    } else
        i = j = out_learnt.size();

    //    stats[max_literals]+=out_learnt.size();
    out_learnt.shrink(i - j);
    //    stats[tot_literals]+=out_learnt.size();


    /* ***************************************
      Minimisation with binary clauses of the asserting clause
      First of all : we look for small clauses
      Then, we reduce clauses with small LBD.
      Otherwise, this can be useless
     */
    if(!incremental && out_learnt.size() <= lbSizeMinimizingClause) {
        minimisationWithBinaryResolution(out_learnt);
    }
    // Find correct backtrack level:
    //
    if(out_learnt.size() == 1)
        out_btlevel = 0;
    else {
        int max_i = 1;
        // Find the first literal assigned at the next-highest level:
        for(int i = 2; i < out_learnt.size(); i++)
            if(level(var(out_learnt[i])) > level(var(out_learnt[max_i])))
                max_i = i;
        // Swap-in this literal at index 1:
        Lit p = out_learnt[max_i];
        out_learnt[max_i] = out_learnt[1];
        out_learnt[1] = p;
        out_btlevel = level(var(p));
    }
#ifdef INCREMENTAL
    if(incremental) {
       szWithoutSelectors = 0;
       for(int i=0;i<out_learnt.size();i++) {
     if(!isSelector(var((out_learnt[i])))) szWithoutSelectors++;
     else if(i>0) break;
       }
     } else
#endif
    szWithoutSelectors = out_learnt.size();

    // Compute LBD
    lbd = computeLBD(out_learnt, out_learnt.size() - selectors.size());

    // UPDATEVARACTIVITY trick (see competition'09 companion paper)
    if(lastDecisionLevel.size() > 0) {
        for(int i = 0; i < lastDecisionLevel.size(); i++) {
            if(ca[reason(var(lastDecisionLevel[i]))].lbd() < lbd)
                varBumpActivity(var(lastDecisionLevel[i]));
        }
        lastDecisionLevel.clear();
    }


    for(int j = 0; j < analyze_toclear.size(); j++) seen[var(analyze_toclear[j])] = 0; // ('seen[]' is now cleared)
    for(int j = 0; j < selectors.size(); j++) seen[var(selectors[j])] = 0;
}


// Check if 'p' can be removed. 'abstract_levels' is used to abort early if the algorithm is
// visiting literals at levels that cannot be removed later.

bool Solver::litRedundant(Lit p, uint32_t abstract_levels) {
    analyze_stack.clear();
    analyze_stack.push(p);
    int top = analyze_toclear.size();
    while(analyze_stack.size() > 0) {
        assert(reason(var(analyze_stack.last())) != CRef_Undef);
        Clause &c = ca[reason(var(analyze_stack.last()))];
        analyze_stack.pop(); //
        if(c.size() == 2 && value(c[0]) == l_False) {
            assert(value(c[1]) == l_True);
            Lit tmp = c[0];
            c[0] = c[1], c[1] = tmp;
        }

        for(int i = 1; i < c.size(); i++) {
            Lit p = c[i];
            if(!seen[var(p)]) {
                if(level(var(p)) > 0) {
                    if(reason(var(p)) != CRef_Undef && (abstractLevel(var(p)) & abstract_levels) != 0) {
                        seen[var(p)] = 1;
                        analyze_stack.push(p);
                        analyze_toclear.push(p);
                    } else {
                        for(int j = top; j < analyze_toclear.size(); j++)
                            seen[var(analyze_toclear[j])] = 0;
                        analyze_toclear.shrink(analyze_toclear.size() - top);
                        return false;
                    }
                }
            }
        }
    }

    return true;
}


/*_________________________________________________________________________________________________
|
|  analyzeFinal : (p : Lit)  ->  [void]
|  
|  Description:
|    Specialized analysis procedure to express the final conflict in terms of assumptions.
|    Calculates the (possibly empty) set of assumptions that led to the assignment of 'p', and
|    stores the result in 'out_conflict'.
|________________________________________________________________________________________________@*/
void Solver::analyzeFinal(Lit p, vec <Lit> &out_conflict) {
    out_conflict.clear();
    out_conflict.push(p);

    if(decisionLevel() == 0)
        return;

    seen[var(p)] = 1;

    for(int i = trail.size() - 1; i >= trail_lim[0]; i--) {
        Var x = var(trail[i]);
        if(seen[x]) {
            if(reason(x) == CRef_Undef) {
                assert(level(x) > 0);
                out_conflict.push(~trail[i]);
            } else {
                Clause &c = ca[reason(x)];
                //                for (int j = 1; j < c.size(); j++) Minisat (glucose 2.0) loop
                // Bug in case of assumptions due to special data structures for Binary.
                // Many thanks to Sam Bayless (sbayless@cs.ubc.ca) for discover this bug.
                for(int j = ((c.size() == 2) ? 0 : 1); j < c.size(); j++)
                    if(level(var(c[j])) > 0)
                        seen[var(c[j])] = 1;
            }

            seen[x] = 0;
        }
    }

    seen[var(p)] = 0;
}


void Solver::uncheckedEnqueue(Lit p, CRef from) {
    assert(value(p) == l_Undef);
    assigns[var(p)] = lbool(!sign(p));
    vardata[var(p)] = mkVarData(from, decisionLevel());
    trail.push_(p);
}


void Solver::bumpForceUNSAT(Lit q) {
    forceUNSAT[var(q)] = sign(q) ? -1 : +1;
    return;
}


/*_________________________________________________________________________________________________
|
|  propagate : [void]  ->  [Clause*]
|  
|  Description:
|    Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
|    otherwise CRef_Undef.
|  
|    Post-conditions:
|      * the propagation queue is empty, even if there was a conflict.
|________________________________________________________________________________________________@*/
CRef Solver::propagate() {
    CRef confl = CRef_Undef;
    int num_props = 0;
    watches.cleanAll();
    watchesBin.cleanAll();
    unaryWatches.cleanAll();
    while(qhead < trail.size()) {
        Lit p = trail[qhead++]; // 'p' is enqueued fact to propagate.
        vec <Watcher> &ws = watches[p];
        Watcher *i, *j, *end;
        num_props++;


        // First, Propagate binary clauses
        vec <Watcher> &wbin = watchesBin[p];
        for(int k = 0; k < wbin.size(); k++) {

            Lit imp = wbin[k].blocker;

            if(value(imp) == l_False) {
                return wbin[k].cref;
            }

            if(value(imp) == l_Undef) {
                uncheckedEnqueue(imp, wbin[k].cref);
            }
        }

        // Now propagate other 2-watched clauses
        for(i = j = (Watcher *) ws, end = i + ws.size(); i != end;) {
            // Try to avoid inspecting the clause:
            Lit blocker = i->blocker;
            if(value(blocker) == l_True) {
                *j++ = *i++;
                continue;
            }

            // Make sure the false literal is data[1]:
            CRef cr = i->cref;
            Clause &c = ca[cr];
            assert(!c.getOneWatched());
            Lit false_lit = ~p;
            if(c[0] == false_lit)
                c[0] = c[1], c[1] = false_lit;
            assert(c[1] == false_lit);
            i++;

            // If 0th watch is true, then clause is already satisfied.
            Lit first = c[0];
            Watcher w = Watcher(cr, first);
            if(first != blocker && value(first) == l_True) {

                *j++ = w;
                continue;
            }
#ifdef INCREMENTAL
            if(incremental) { // ----------------- INCREMENTAL MODE
              int choosenPos = -1;
              for (int k = 2; k < c.size(); k++) {

            if (value(c[k]) != l_False){
              if(decisionLevel()>assumptions.size()) {
                choosenPos = k;
                break;
              } else {
                choosenPos = k;

                if(value(c[k])==l_True || !isSelector(var(c[k]))) {
                  break;
                }
              }

            }
              }
              if(choosenPos!=-1) {
            c[1] = c[choosenPos]; c[choosenPos] = false_lit;
            watches[~c[1]].push(w);
            goto NextClause; }
            } else {  // ----------------- DEFAULT  MODE (NOT INCREMENTAL)
#endif
            for(int k = 2; k < c.size(); k++) {

                if(value(c[k]) != l_False) {
                    c[1] = c[k];
                    c[k] = false_lit;
                    watches[~c[1]].push(w);
                    goto NextClause;
                }
            }
#ifdef INCREMENTAL
            }
#endif
            // Did not find watch -- clause is unit under assignment:
            *j++ = w;
            if(value(first) == l_False) {
                confl = cr;
                qhead = trail.size();
                // Copy the remaining watches:
                while(i < end)
                    *j++ = *i++;
            } else {
                uncheckedEnqueue(first, cr);


            }
            NextClause:;
        }
        ws.shrink(i - j);

        // unaryWatches "propagation"
        if(useUnaryWatched && confl == CRef_Undef) {
            confl = propagateUnaryWatches(p);

        }

    }


    propagations += num_props;
    simpDB_props -= num_props;

    return confl;
}


/*_________________________________________________________________________________________________
|
|  propagateUnaryWatches : [Lit]  ->  [Clause*]
|  
|  Description:
|    Propagates unary watches of Lit p, return a conflict 
|    otherwise CRef_Undef
|  
|________________________________________________________________________________________________@*/

CRef Solver::propagateUnaryWatches(Lit p) {
    CRef confl = CRef_Undef;
    Watcher *i, *j, *end;
    vec <Watcher> &ws = unaryWatches[p];
    for(i = j = (Watcher *) ws, end = i + ws.size(); i != end;) {
        // Try to avoid inspecting the clause:
        Lit blocker = i->blocker;
        if(value(blocker) == l_True) {
            *j++ = *i++;
            continue;
        }

        // Make sure the false literal is data[1]:
        CRef cr = i->cref;
        Clause &c = ca[cr];
        assert(c.getOneWatched());
        Lit false_lit = ~p;
        assert(c[0] == false_lit); // this is unary watch... No other choice if "propagated"
        //if (c[0] == false_lit)
        //c[0] = c[1], c[1] = false_lit;
        //assert(c[1] == false_lit);
        i++;
        Watcher w = Watcher(cr, c[0]);
        for(int k = 1; k < c.size(); k++) {
            if(value(c[k]) != l_False) {
                c[0] = c[k];
                c[k] = false_lit;
                unaryWatches[~c[0]].push(w);
                goto NextClauseUnary;
            }
        }

        // Did not find watch -- clause is empty under assignment:
        *j++ = w;

        confl = cr;
        qhead = trail.size();
        // Copy the remaining watches:
        while(i < end)
            *j++ = *i++;

        // We can add it now to the set of clauses when backtracking
        //printf("*");
        if(promoteOneWatchedClause) {
            stats[nbPromoted]++;
            // Let's find the two biggest decision levels in the clause s.t. it will correctly be propagated when we'll backtrack
            int maxlevel = -1;
            int index = -1;
            for(int k = 1; k < c.size(); k++) {
                assert(value(c[k]) == l_False);
                assert(level(var(c[k])) <= level(var(c[0])));
                if(level(var(c[k])) > maxlevel) {
                    index = k;
                    maxlevel = level(var(c[k]));
                }
            }
            detachClausePurgatory(cr, true); // TODO: check that the cleanAll is ok (use ",true" otherwise)
            assert(index != -1);
            Lit tmp = c[1];
            c[1] = c[index], c[index] = tmp;
            attachClause(cr);
            // TODO used in function ParallelSolver::reportProgressArrayImports
            //Override :-(
            //goodImportsFromThreads[ca[cr].importedFrom()]++;
            ca[cr].setOneWatched(false);
            ca[cr].setExported(2);
        }
        NextClauseUnary:;
    }
    ws.shrink(i - j);

    return confl;
}


/*_________________________________________________________________________________________________
|
|  reduceDB : ()  ->  [void]
|  
|  Description:
|    Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
|    clauses are clauses that are reason to some assignment. Binary clauses are never removed.
|________________________________________________________________________________________________@*/


void Solver::reduceDB() {

    int i, j;
    stats[nbReduceDB]++;
    if(chanseokStrategy)
        sort(learnts, reduceDBAct_lt(ca));
    else {
        sort(learnts, reduceDB_lt(ca));

        // We have a lot of "good" clauses, it is difficult to compare them. Keep more !
        if(ca[learnts[learnts.size() / RATIOREMOVECLAUSES]].lbd() <= 3) nbclausesbeforereduce += specialIncReduceDB;
        // Useless :-)
        if(ca[learnts.last()].lbd() <= 5) nbclausesbeforereduce += specialIncReduceDB;

    }
    // Don't delete binary or locked clauses. From the rest, delete clauses from the first half
    // Keep clauses which seem to be usefull (their lbd was reduce during this sequence)

    int limit = learnts.size() / 2;

    for(i = j = 0; i < learnts.size(); i++) {
        Clause &c = ca[learnts[i]];
        if(c.lbd() > 2 && c.size() > 2 && c.canBeDel() && !locked(c) && (i < limit)) {
            removeClause(learnts[i]);
            stats[nbRemovedClauses]++;
        }
        else {
            if(!c.canBeDel()) limit++; //we keep c, so we can delete an other clause
            c.setCanBeDel(true);       // At the next step, c can be delete
            learnts[j++] = learnts[i];
        }
    }
    learnts.shrink(i - j);
    checkGarbage();
}


void Solver::removeSatisfied(vec <CRef> &cs) {

    int i, j;
    for(i = j = 0; i < cs.size(); i++) {
        Clause &c = ca[cs[i]];


        if(satisfied(c)) if(c.getOneWatched())
            removeClause(cs[i], true);
        else
            removeClause(cs[i]);
        else
            cs[j++] = cs[i];
    }
    cs.shrink(i - j);
}


void Solver::rebuildOrderHeap() {
    vec <Var> vs;
    for(Var v = 0; v < nVars(); v++)
        if(decision[v] && value(v) == l_Undef)
            vs.push(v);
    order_heap.build(vs);

}


/*_________________________________________________________________________________________________
|
|  simplify : [void]  ->  [bool]
|  
|  Description:
|    Simplify the clause database according to the current top-level assigment. Currently, the only
|    thing done here is the removal of satisfied clauses, but more things can be put here.
|________________________________________________________________________________________________@*/
bool Solver::simplify() {
    assert(decisionLevel() == 0);

    if(!ok) return ok = false;
    else {
        CRef cr = propagate();
        if(cr != CRef_Undef) {
            return ok = false;
        }
    }


    if(nAssigns() == simpDB_assigns || (simpDB_props > 0))
        return true;

    // Remove satisfied clauses:
    removeSatisfied(learnts);
    removeSatisfied(permanentLearnts);
    removeSatisfied(unaryWatchedClauses);
    if(remove_satisfied) // Can be turned off.
        removeSatisfied(clauses);
    checkGarbage();
    rebuildOrderHeap();

    simpDB_assigns = nAssigns();
    simpDB_props = stats[clauses_literals] + stats[learnts_literals]; // (shouldn't depend on stats really, but it will do for now)

    return true;
}


void Solver::adaptSolver() {
    bool adjusted = false;
    bool reinit = false;
    printf("c\nc Try to adapt solver strategies\nc \n");
    /*  printf("c Adjusting solver for the SAT Race 2015 (alpha feature)\n");
    printf("c key successive Conflicts       : %" PRIu64"\n",stats[noDecisionConflict]);
    printf("c nb unary clauses learnt        : %" PRIu64"\n",stats[nbUn]);
    printf("c key avg dec per conflicts      : %.2f\n", (float)decisions / (float)conflicts);*/
    float decpc = (float) decisions / (float) conflicts;
    if(decpc <= 1.2) {
        chanseokStrategy = true;
        coLBDBound = 4;
        glureduce = true;
        adjusted = true;
        printf("c Adjusting for low decision levels.\n");
        reinit = true;
        firstReduceDB = 2000;
        nbclausesbeforereduce = firstReduceDB;
        curRestart = (conflicts / nbclausesbeforereduce) + 1;
        incReduceDB = 0;
    }
    if(stats[noDecisionConflict] < 30000) {
        luby_restart = true;
        luby_restart_factor = 100;

        var_decay = 0.999;
        max_var_decay = 0.999;
        adjusted = true;
        printf("c Adjusting for low successive conflicts.\n");
    }
    if(stats[noDecisionConflict] > 54400) {
        printf("c Adjusting for high successive conflicts.\n");
        chanseokStrategy = true;
        glureduce = true;
        coLBDBound = 3;
        firstReduceDB = 30000;
        var_decay = 0.99;
        max_var_decay = 0.99;
        randomize_on_restarts = 1;
        adjusted = true;
    }
    if(stats[nbDL2] - stats[nbBin] > 20000) {
        var_decay = 0.91;
        max_var_decay = 0.91;
        adjusted = true;
        printf("c Adjusting for a very large number of true glue clauses found.\n");
    }
    if(!adjusted) {
        printf("c Nothing extreme in this problem, continue with glucose default strategies.\n");
    }
    printf("c\n");
    if(adjusted) { // Let's reinitialize the glucose restart strategy counters
        lbdQueue.fastclear();
        sumLBD = 0;
        conflictsRestarts = 0;
    }

    if(chanseokStrategy && adjusted) {
        int moved = 0;
        int i, j;
        for(i = j = 0; i < learnts.size(); i++) {
            Clause &c = ca[learnts[i]];
            if(c.lbd() <= coLBDBound) {
                permanentLearnts.push(learnts[i]);
                moved++;
            }
            else {
                learnts[j++] = learnts[i];
            }
        }
        learnts.shrink(i - j);
        printf("c Activating Chanseok Strategy: moved %d clauses to the permanent set.\n", moved);
    }

    if(reinit) {
        assert(decisionLevel() == 0);
        for(int i = 0; i < learnts.size(); i++) {
            removeClause(learnts[i]);
        }
        learnts.shrink(learnts.size());
        checkGarbage();
/*
	order_heap.clear();
	for(int i=0;i<nVars();i++) {
	    polarity[i] = true; 
	    activity[i]=0.0;
	    if (decision[i]) order_heap.insert(i);
	}
	printf("c reinitialization of all variables activity/phase/learnt clauses.\n");
*/
        printf("c Removing of non permanent clauses.\n");
    }

}


/*_________________________________________________________________________________________________
|
|  search : (nof_conflicts : int) (params : const SearchParams&)  ->  [lbool]
|  
|  Description:
|    Search for a model the specified number of conflicts. 
|    NOTE! Use negative value for 'nof_conflicts' indicate infinity.
|  
|  Output:
|    'l_True' if a partial assigment that is consistent with respect to the clauseset is found. If
|    all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
|    if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
|________________________________________________________________________________________________@*/
lbool Solver::search(int nof_conflicts) {
    assert(ok);
    int backtrack_level;
    int conflictC = 0;
    vec <Lit> learnt_clause, selectors;
    unsigned int nblevels, szWithoutSelectors = 0;
    bool blocked = false;
    bool aDecisionWasMade = false;

    starts++;
    for(; ;) {
        if(decisionLevel() == 0) { // We import clauses FIXME: ensure that we will import clauses enventually (restart after some point)
            parallelImportUnaryClauses();

            if(parallelImportClauses())
                return l_False;

        }
        CRef confl = propagate();

        if(confl != CRef_Undef) {
            newDescent = false;
            if(parallelJobIsFinished())
                return l_Undef;

            if(!aDecisionWasMade)
                stats[noDecisionConflict]++;
            aDecisionWasMade = false;

            stats[sumDecisionLevels] += decisionLevel();
            stats[sumTrail] += trail.size();
            // CONFLICT
            conflicts++;
            conflictC++;
            conflictsRestarts++;
            if(conflicts % 5000 == 0 && var_decay < max_var_decay)
                var_decay += 0.01;

            if(verbosity >= 1 && starts>0 && conflicts % verbEveryConflicts == 0) {
                printf("c | %8d   %7d    %5d | %7d %8d %8d | %5d %8d   %6d %8d | %6.3f %% |\n",
                       (int) starts, (int) stats[nbstopsrestarts], (int) (conflicts / starts),
                       (int) stats[dec_vars] - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]), nClauses(), (int) stats[clauses_literals],
                       (int) stats[nbReduceDB], nLearnts(), (int) stats[nbDL2], (int) stats[nbRemovedClauses], progressEstimate() * 100);
            }
            if(decisionLevel() == 0) {
                return l_False;

            }
            if(adaptStrategies && conflicts == 100000) {
                cancelUntil(0);
                adaptSolver();
                adaptStrategies = false;
                return l_Undef;
            }

            trailQueue.push(trail.size());
            // BLOCK RESTART (CP 2012 paper)
            if(conflictsRestarts > LOWER_BOUND_FOR_BLOCKING_RESTART && lbdQueue.isvalid() && trail.size() > R * trailQueue.getavg()) {
                lbdQueue.fastclear();
                stats[nbstopsrestarts]++;
                if(!blocked) {
                    stats[lastblockatrestart] = starts;
                    stats[nbstopsrestartssame]++;
                    blocked = true;
                }
            }

            learnt_clause.clear();
            selectors.clear();

            analyze(confl, learnt_clause, selectors, backtrack_level, nblevels, szWithoutSelectors);

            lbdQueue.push(nblevels);
            sumLBD += nblevels;

            cancelUntil(backtrack_level);

            if(certifiedUNSAT) {
                if(vbyte) {
                    write_char('a');
                    for(int i = 0; i < learnt_clause.size(); i++)
                        write_lit(2 * (var(learnt_clause[i]) + 1) + sign(learnt_clause[i]));
                    write_lit(0);
                }
                else {
                    for(int i = 0; i < learnt_clause.size(); i++)
                        fprintf(certifiedOutput, "%i ", (var(learnt_clause[i]) + 1) *
                                                        (-2 * sign(learnt_clause[i]) + 1));
                    fprintf(certifiedOutput, "0\n");
                }
            }


            if(learnt_clause.size() == 1) {
                uncheckedEnqueue(learnt_clause[0]);
                stats[nbUn]++;
                parallelExportUnaryClause(learnt_clause[0]);
            } else {
                CRef cr;
                if(chanseokStrategy && nblevels <= coLBDBound) {
                    cr = ca.alloc(learnt_clause, false);
                    permanentLearnts.push(cr);
                    stats[nbPermanentLearnts]++;
                } else {
                    cr = ca.alloc(learnt_clause, true);
                    ca[cr].setLBD(nblevels);
                    ca[cr].setOneWatched(false);
                    learnts.push(cr);
                    claBumpActivity(ca[cr]);
                }
#ifdef INCREMENTAL
                ca[cr].setSizeWithoutSelectors(szWithoutSelectors);
#endif
                if(nblevels <= 2) { stats[nbDL2]++; } // stats
                if(ca[cr].size() == 2) stats[nbBin]++; // stats
                attachClause(cr);
                lastLearntClause = cr; // Use in multithread (to hard to put inside ParallelSolver)
                parallelExportClauseDuringSearch(ca[cr]);
                uncheckedEnqueue(learnt_clause[0], cr);

            }
            varDecayActivity();
            claDecayActivity();


        } else {
            // Our dynamic restart, see the SAT09 competition compagnion paper
            if((luby_restart && nof_conflicts <= conflictC) ||
               (!luby_restart && (lbdQueue.isvalid() && ((lbdQueue.getavg() * K) > (sumLBD / conflictsRestarts))))) {
                lbdQueue.fastclear();
                progress_estimate = progressEstimate();
                int bt = 0;
#ifdef INCREMENTAL
                if(incremental) // DO NOT BACKTRACK UNTIL 0.. USELESS
                    bt = (decisionLevel()<assumptions.size()) ? decisionLevel() : assumptions.size();
#endif
                newDescent = true;

                if(randomize_on_restarts || fixed_randomize_on_restarts) {
                    randomDescentAssignments = (uint32_t) drand(random_seed);
                }

                cancelUntil(bt);
                return l_Undef;
            }


            // Simplify the set of problem clauses:
            if(decisionLevel() == 0 && !simplify()) {
                return l_False;
            }
            // Perform clause database reduction !
            if((chanseokStrategy && !glureduce && learnts.size() > firstReduceDB) ||
               (glureduce && conflicts >= ((unsigned int) curRestart * nbclausesbeforereduce))) {

                if(learnts.size() > 0) {
                    curRestart = (conflicts / nbclausesbeforereduce) + 1;
                    reduceDB();
                    if(!panicModeIsEnabled())
                        nbclausesbeforereduce += incReduceDB;
                }
            }

            lastLearntClause = CRef_Undef;
            Lit next = lit_Undef;
            while(decisionLevel() < assumptions.size()) {
                // Perform user provided assumption:
                Lit p = assumptions[decisionLevel()];
                if(value(p) == l_True) {
                    // Dummy decision level:
                    newDecisionLevel();
                } else if(value(p) == l_False) {
                    analyzeFinal(~p, conflict);
                    return l_False;
                } else {
                    next = p;
                    break;
                }
            }

            if(next == lit_Undef) {
                // New variable decision:
                decisions++;
                next = pickBranchLit();
                if(next == lit_Undef) {
                    //printf("c last restart ## conflicts  :  %d %d \n", conflictC, decisionLevel());
                    // Model found:
                    return l_True;
                }
            }

            // Increase decision level and enqueue 'next'
            aDecisionWasMade = true;
            newDecisionLevel();
            uncheckedEnqueue(next);
        }
    }
}


double Solver::progressEstimate() const {
    double progress = 0;
    double F = 1.0 / nVars();

    for(int i = 0; i <= decisionLevel(); i++) {
        int beg = i == 0 ? 0 : trail_lim[i - 1];
        int end = i == decisionLevel() ? trail.size() : trail_lim[i];
        progress += pow(F, i) * (end - beg);
    }

    return progress / nVars();
}


void Solver::printIncrementalStats() {

    printf("c---------- Glucose Stats -------------------------\n");
    printf("c restarts              : %"
    PRIu64
    "\n", starts);
    printf("c nb ReduceDB           : %"
    PRIu64
    "\n", stats[nbReduceDB]);
    printf("c nb removed Clauses    : %"
    PRIu64
    "\n", stats[nbRemovedClauses]);
    printf("c nb learnts DL2        : %"
    PRIu64
    "\n", stats[nbDL2]);
    printf("c nb learnts size 2     : %"
    PRIu64
    "\n", stats[nbBin]);
    printf("c nb learnts size 1     : %"
    PRIu64
    "\n", stats[nbUn]);

    printf("c conflicts             : %"
    PRIu64
    "\n", conflicts);
    printf("c decisions             : %"
    PRIu64
    "\n", decisions);
    printf("c propagations          : %"
    PRIu64
    "\n", propagations);

    printf("\nc SAT Calls             : %d in %g seconds\n", nbSatCalls, totalTime4Sat);
    printf("c UNSAT Calls           : %d in %g seconds\n", nbUnsatCalls, totalTime4Unsat);

    printf("c--------------------------------------------------\n");
}


double Solver::luby(double y, int x) {

    // Find the finite subsequence that contains index 'x', and the
    // size of that subsequence:
    int size, seq;
    for(size = 1, seq = 0; size < x + 1; seq++, size = 2 * size + 1);

    while(size - 1 != x) {
        size = (size - 1) >> 1;
        seq--;
        x = x % size;
    }

    return pow(y, seq);
}


// NOTE: assumptions passed in member-variable 'assumptions'.

lbool Solver::solve_(bool do_simp, bool turn_off_simp) // Parameters are useless in core but useful for SimpSolver....
{

    if(incremental && certifiedUNSAT) {
        printf("Can not use incremental and certified unsat in the same time\n");
        exit(-1);
    }

    model.clear();
    conflict.clear();
    if(!ok) return l_False;
    double curTime = cpuTime();

    solves++;


    lbool status = l_Undef;
    if(!incremental && verbosity >= 1) {
        printf("c ========================================[ MAGIC CONSTANTS ]==============================================\n");
        printf("c | Constants are supposed to work well together :-)                                                      |\n");
        printf("c | however, if you find better choices, please let us known...                                           |\n");
        printf("c |-------------------------------------------------------------------------------------------------------|\n");
        if(adaptStrategies) {
            printf("c | Adapt dynamically the solver after 100000 conflicts (restarts, reduction strategies...)               |\n");
            printf("c |-------------------------------------------------------------------------------------------------------|\n");
        }
        printf("c |                                |                                |                                     |\n");
        printf("c | - Restarts:                    | - Reduce Clause DB:            | - Minimize Asserting:               |\n");
        if(chanseokStrategy) {
            printf("c |   * LBD Queue    : %6d      |     chanseok Strategy          |    * size < %3d                     |\n", lbdQueue.maxSize(),
                   lbSizeMinimizingClause);
            printf("c |   * Trail  Queue : %6d      |   * learnts size     : %6d  |    * lbd  < %3d                     |\n", trailQueue.maxSize(),
                   firstReduceDB, lbLBDMinimizingClause);
            printf("c |   * K            : %6.2f      |   * Bound LBD   : %6d       |                                     |\n", K, coLBDBound);
            printf("c |   * R            : %6.2f      |   * Protected :  (lbd)< %2d     |                                     |\n", R, lbLBDFrozenClause);
        } else {
            printf("c |   * LBD Queue    : %6d      |   * First     : %6d         |    * size < %3d                     |\n", lbdQueue.maxSize(),
                   nbclausesbeforereduce, lbSizeMinimizingClause);
            printf("c |   * Trail  Queue : %6d      |   * Inc       : %6d         |    * lbd  < %3d                     |\n", trailQueue.maxSize(), incReduceDB,
                   lbLBDMinimizingClause);
            printf("c |   * K            : %6.2f      |   * Special   : %6d         |                                     |\n", K, specialIncReduceDB);
            printf("c |   * R            : %6.2f      |   * Protected :  (lbd)< %2d     |                                     |\n", R, lbLBDFrozenClause);
        }
        printf("c |                                |                                |                                     |\n");
        printf("c ==================================[ Search Statistics (every %6d conflicts) ]=========================\n", verbEveryConflicts);
        printf("c |                                                                                                       |\n");

        printf("c |          RESTARTS           |          ORIGINAL         |              LEARNT              | Progress |\n");
        printf("c |       NB   Blocked  Avg Cfc |    Vars  Clauses Literals |   Red   Learnts    LBD2  Removed |          |\n");
        printf("c =========================================================================================================\n");
    }

    // Search:
    int curr_restarts = 0;
    while(status == l_Undef) {
        status = search(
                luby_restart ? luby(restart_inc, curr_restarts) * luby_restart_factor : 0); // the parameter is useless in glucose, kept to allow modifications

        if(!withinBudget()) break;
        curr_restarts++;
    }

    if(!incremental && verbosity >= 1)
        printf("c =========================================================================================================\n");

    if(certifiedUNSAT) { // Want certified output
        if(status == l_False) {
            if(vbyte) {
                write_char('a');
                write_lit(0);
            }
            else {
                fprintf(certifiedOutput, "0\n");
            }
        }
        fclose(certifiedOutput);
    }


    if(status == l_True) {
        // Extend & copy model:
        model.growTo(nVars());
        for(int i = 0; i < nVars(); i++) model[i] = value(i);
    } else if(status == l_False && conflict.size() == 0)
        ok = false;


    cancelUntil(0);


    double finalTime = cpuTime();
    if(status == l_True) {
        nbSatCalls++;
        totalTime4Sat += (finalTime - curTime);
    }
    if(status == l_False) {
        nbUnsatCalls++;
        totalTime4Unsat += (finalTime - curTime);
    }


    return status;

}





//=================================================================================================
// Writing CNF to DIMACS:
// 
// FIXME: this needs to be rewritten completely.

static Var mapVar(Var x, vec <Var> &map, Var &max) {
    if(map.size() <= x || map[x] == -1) {
        map.growTo(x + 1, -1);
        map[x] = max++;
    }
    return map[x];
}


void Solver::toDimacs(FILE *f, Clause &c, vec <Var> &map, Var &max) {
    if(satisfied(c)) return;

    for(int i = 0; i < c.size(); i++)
        if(value(c[i]) != l_False)
            fprintf(f, "%s%d ", sign(c[i]) ? "-" : "", mapVar(var(c[i]), map, max) + 1);
    fprintf(f, "0\n");
}


void Solver::toDimacs(const char *file, const vec <Lit> &assumps) {
    FILE *f = fopen(file, "wr");
    if(f == NULL)
        fprintf(stderr, "could not open file %s\n", file), exit(1);
    toDimacs(f, assumps);
    fclose(f);
}


void Solver::toDimacs(FILE *f, const vec <Lit> &assumps) {
    // Handle case when solver is in contradictory state:
    if(!ok) {
        fprintf(f, "p cnf 1 2\n1 0\n-1 0\n");
        return;
    }

    vec <Var> map;
    Var max = 0;

    // Cannot use removeClauses here because it is not safe
    // to deallocate them at this point. Could be improved.
    int cnt = 0;
    for(int i = 0; i < clauses.size(); i++)
        if(!satisfied(ca[clauses[i]]))
            cnt++;

    for(int i = 0; i < clauses.size(); i++)
        if(!satisfied(ca[clauses[i]])) {
            Clause &c = ca[clauses[i]];
            for(int j = 0; j < c.size(); j++)
                if(value(c[j]) != l_False)
                    mapVar(var(c[j]), map, max);
        }

    // Assumptions are added as unit clauses:
    cnt += assumptions.size();

    fprintf(f, "p cnf %d %d\n", max, cnt);

    for(int i = 0; i < assumptions.size(); i++) {
        assert(value(assumptions[i]) != l_False);
        fprintf(f, "%s%d 0\n", sign(assumptions[i]) ? "-" : "", mapVar(var(assumptions[i]), map, max) + 1);
    }

    for(int i = 0; i < clauses.size(); i++)
        toDimacs(f, ca[clauses[i]], map, max);

    if(verbosity > 0)
        printf("Wrote %d clauses with %d variables.\n", cnt, max);
}


//=================================================================================================
// Garbage Collection methods:

void Solver::relocAll(ClauseAllocator &to) {
    // All watchers:
    // for (int i = 0; i < watches.size(); i++)
    watches.cleanAll();
    watchesBin.cleanAll();
    unaryWatches.cleanAll();
    for(int v = 0; v < nVars(); v++)
        for(int s = 0; s < 2; s++) {
            Lit p = mkLit(v, s);
            // printf(" >>> RELOCING: %s%d\n", sign(p)?"-":"", var(p)+1);
            vec <Watcher> &ws = watches[p];
            for(int j = 0; j < ws.size(); j++)
                ca.reloc(ws[j].cref, to);
            vec <Watcher> &ws2 = watchesBin[p];
            for(int j = 0; j < ws2.size(); j++)
                ca.reloc(ws2[j].cref, to);
            vec <Watcher> &ws3 = unaryWatches[p];
            for(int j = 0; j < ws3.size(); j++)
                ca.reloc(ws3[j].cref, to);
        }

    // All reasons:
    //
    for(int i = 0; i < trail.size(); i++) {
        Var v = var(trail[i]);

        if(reason(v) != CRef_Undef && (ca[reason(v)].reloced() || locked(ca[reason(v)])))
            ca.reloc(vardata[v].reason, to);
    }

    // All learnt:
    //
    for(int i = 0; i < learnts.size(); i++)
        ca.reloc(learnts[i], to);

    for(int i = 0; i < permanentLearnts.size(); i++)
        ca.reloc(permanentLearnts[i], to);

    // All original:
    //
    for(int i = 0; i < clauses.size(); i++)
        ca.reloc(clauses[i], to);

    for(int i = 0; i < unaryWatchedClauses.size(); i++)
        ca.reloc(unaryWatchedClauses[i], to);
}


void Solver::garbageCollect() {
    // Initialize the next region to a size corresponding to the estimated utilization degree. This
    // is not precise but should avoid some unnecessary reallocations for the new region:
    ClauseAllocator to(ca.size() - ca.wasted());
    relocAll(to);
    if(verbosity >= 2)
        printf("|  Garbage collection:   %12d bytes => %12d bytes             |\n",
               ca.size() * ClauseAllocator::Unit_Size, to.size() * ClauseAllocator::Unit_Size);
    to.moveTo(ca);
}

//--------------------------------------------------------------
// Functions related to MultiThread.
// Useless in case of single core solver (aka original glucose)
// Keep them empty if you just use core solver
//--------------------------------------------------------------

bool Solver::panicModeIsEnabled() {
    return false;
}


void Solver::parallelImportUnaryClauses() {
}


bool Solver::parallelImportClauses() {
    return false;
}


void Solver::parallelExportUnaryClause(Lit p) {
}


void Solver::parallelExportClauseDuringSearch(Clause &c) {
}


bool Solver::parallelJobIsFinished() {
    // Parallel: another job has finished let's quit
    return false;
}


void Solver::parallelImportClauseDuringConflictAnalysis(Clause &c, CRef confl) {
}
