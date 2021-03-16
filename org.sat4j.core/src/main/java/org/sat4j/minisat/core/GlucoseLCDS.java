/*******************************************************************************
 * SAT4J: a SATisfiability library for Java Copyright (C) 2004, 2012 Artois University and CNRS
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 *  http://www.eclipse.org/legal/epl-v10.html
 *
 * Alternatively, the contents of this file may be used under the terms of
 * either the GNU Lesser General Public License Version 2.1 or later (the
 * "LGPL"), in which case the provisions of the LGPL are applicable instead
 * of those above. If you wish to allow use of your version of this file only
 * under the terms of the LGPL, and not to allow others to use your version of
 * this file under the terms of the EPL, indicate your decision by deleting
 * the provisions above and replace them with the notice and other provisions
 * required by the LGPL. If you do not delete the provisions above, a recipient
 * may use your version of this file under the terms of the EPL or the LGPL.
 *
 * Based on the original MiniSat specification from:
 *
 * An extensible SAT solver. Niklas Een and Niklas Sorensson. Proceedings of the
 * Sixth International Conference on Theory and Applications of Satisfiability
 * Testing, LNCS 2919, pp 502-518, 2003.
 *
 * See www.minisat.se for the original solver in C++.
 *
 * Contributors:
 *   CRIL - initial API and implementation
 *******************************************************************************/
package org.sat4j.minisat.core;

import org.sat4j.annotations.Feature;
import org.sat4j.specs.Constr;
import org.sat4j.specs.IVec;

/**
 * LBD based clauses cleaning strategy, as found in Glucose.
 *
 * This strategy expects the constraints to be clauses, i.e. the LBD computation
 * may not be correct for other constraints (cardinality constraints, PB
 * constraints).
 *
 * @author leberre
 *
 * @param <D>
 */
@Feature(value = "deletion", parent = "expert")
class GlucoseLCDS<D extends DataStructureFactory>
        implements LearnedConstraintsDeletionStrategy {

    /**
     *
     */
    protected final Solver<D> solver;
    private static final long serialVersionUID = 1L;
    private int[] flags = new int[0];
    private int flag = 0;
    // private int wall = 0;

    private final ConflictTimer timer;

    protected GlucoseLCDS(Solver<D> solver, ConflictTimer timer) {
        this.solver = solver;
        this.timer = timer;
    }

    public void reduce(IVec<Constr> learnedConstrs) {
        learnedConstrs.sort(solver.getActivityComparator());
        int i, j;
        for (i = j = learnedConstrs.size() / 2; i < learnedConstrs
                .size(); i++) {
            Constr c = learnedConstrs.get(i);
            if (c.locked() || c.getActivity() <= 2.0) {
                learnedConstrs.set(j++, learnedConstrs.get(i));
            } else {
                c.remove(solver);
                solver.slistener.delete(c);
                onRemove(c);
            }
        }
        if (solver.isVerbose()) {
            solver.out.log(this.solver.getLogPrefix() + "cleaning " //$NON-NLS-1$
                    + (learnedConstrs.size() - j) + " clauses out of " //$NON-NLS-1$
                    + learnedConstrs.size() + " with flag " //$NON-NLS-1$
                    + this.flag + "/" + solver.stats.getConflicts());
            // out.flush();
        }
        learnedConstrs.shrinkTo(j);

    }

    protected void onRemove(Constr c) {
        // Nothing to do by default.
    }

    public ConflictTimer getTimer() {
        return this.timer;
    }

    @Override
    public String toString() {
        return "Glucose learned constraints deletion strategy with timer "
                + timer;
    }

    public void init() {
        final int howmany = solver.voc.nVars();
        // wall = constrs.size() > 10000 ? constrs.size() : 10000;
        if (this.flags.length <= howmany) {
            this.flags = new int[howmany + 1];
        }
        this.flag = 0;
        this.timer.reset();
    }

    public void onClauseLearning(Constr constr) {
        int nblevel = computeLBD(constr, -1);
        constr.setActivity(nblevel);
    }

    protected int computeLBD(Constr constr, int propagated) {
        int nblevel = 1;
        this.flag++;
        int currentLevel;
        for (int i = 1; i < constr.size(); i++) {
            currentLevel = solver.voc.getLevel(constr.get(i));
            if (currentLevel >= 0 && this.flags[currentLevel] != this.flag) {
                this.flags[currentLevel] = this.flag;
                nblevel++;
            }
        }
        return nblevel;
    }

    public void onConflictAnalysis(Constr reason) {

    }

    public void onPropagation(Constr from, int propagated) {

    }

    protected Solver<D> getSolver() {
        return solver;
    }
}
