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

import static org.sat4j.core.LiteralsUtils.toDimacs;
import static org.sat4j.core.LiteralsUtils.toInternal;
import static org.sat4j.core.LiteralsUtils.var;

import java.util.Comparator;

import org.sat4j.annotations.Feature;
import org.sat4j.core.VecInt;
import org.sat4j.specs.Constr;
import org.sat4j.specs.IVec;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.MandatoryLiteralListener;
import org.sat4j.specs.Propagatable;

/**
 * Watcher based implementation of the model minimization strategy to compute a
 * prime implicant. The main advantage of this method is to be linear in the
 * size (in number of literals) of the formula as long as a specific property
 * holds for the constraints. That approach also takes advantage of the lazy
 * data structures found in modern SAT solvers See our FMCAD 2013 paper for
 * details.
 * 
 * @author leberre
 * 
 */
@Feature(value = "primeimplicant", parent = "expert")
public class WatcherBasedPrimeImplicantStrategy
        implements PrimeImplicantStrategy, MandatoryLiteralListener {

    private int[] prime;

    private final Comparator<Integer> comparator;

    public WatcherBasedPrimeImplicantStrategy(Comparator<Integer> comparator) {
        this.comparator = comparator;
    }

    public WatcherBasedPrimeImplicantStrategy() {
        this(null);
    }

    public void isMandatory(int p) {
        prime[var(p)] = toDimacs(p);
    }

    public int[] compute(Solver<? extends DataStructureFactory> solver) {
        assert solver.qhead == solver.trail.size()
                + solver.learnedLiterals.size();
        long begin = System.currentTimeMillis();
        if (solver.learnedLiterals.size() > 0) {
            solver.qhead = solver.trail.size();
        }
        this.prime = new int[solver.voc.nVars() + 1];
        int p;
        for (int i = 0; i < this.prime.length; i++) {
            this.prime[i] = 0;
        }
        // unit clauses need to be handled specifically
        for (int i = 0; i < solver.trail.size(); i++) {
            isMandatory(solver.trail.get(i));
        }
        for (int d : solver.fullmodel) {
            p = toInternal(d);
            if (solver.voc.isUnassigned(p)) {
                solver.assume(p);
            }
        }
        for (int d : solver.fullmodel) {
            reduceClausesContainingTheNegationOfPI(solver, toInternal(d));
        }

        int removed = 0;
        int posremoved = 0;
        int propagated = 0;
        for (int d : fullModel(solver)) {
            if (this.prime[Math.abs(d)] != 0) {
                // d has been propagated
                propagated++;
            } else {
                // it is not a mandatory literal
                solver.forget(Math.abs(d));
                reduceClausesContainingTheNegationOfPI(solver, toInternal(-d));
                removed++;
                if (d > 0 && d > solver.nVars()) {
                    posremoved++;
                }
            }
        }
        solver.cancelUntil(0);
        int[] implicant = new int[propagated];
        int index = 0;
        for (int i : this.prime) {
            if (i != 0) {
                implicant[index++] = i;
            }
        }
        long end = System.currentTimeMillis();
        if (solver.isVerbose()) {
            System.out.printf(
                    "%s prime implicant computation statistics BRESIL (reverse = %b)%n",
                    solver.getLogPrefix(), this.comparator != null);
            System.out.printf(
                    "%s implied: %d, decision: %d, removed %d (+%d), propagated %d, time(ms):%d %n",
                    solver.getLogPrefix(), solver.implied.size(),
                    solver.decisions.size(), removed, posremoved, propagated,
                    end - begin);
        }
        return implicant;
    }

    Constr reduceClausesContainingTheNegationOfPI(
            Solver<? extends DataStructureFactory> solver, int p) {
        assert p > 1;
        IVec<Propagatable> lwatched = solver.watched;
        lwatched.clear();
        solver.voc.watches(p).moveTo(lwatched);
        final int size = lwatched.size();
        for (int i = 0; i < size; i++) {
            solver.stats.incInspects();
            lwatched.get(i).propagatePI(this, p);
        }
        return null;
    }

    public int[] getPrimeImplicantAsArrayWithHoles() {
        if (prime == null) {
            throw new UnsupportedOperationException(
                    "Call the compute method first!");
        }
        return prime;
    }

    private int[] fullModel(Solver<? extends DataStructureFactory> solver) {
        if (this.comparator == null) {
            return solver.fullmodel;
        }
        int n = solver.fullmodel.length;
        IVecInt reversed = new VecInt(n);
        for (int i : solver.fullmodel) {
            reversed.push(i);
        }
        reversed.sort(comparator);
        return reversed.toArray();
    }
}
