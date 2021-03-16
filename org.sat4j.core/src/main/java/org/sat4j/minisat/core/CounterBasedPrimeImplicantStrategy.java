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

import static org.sat4j.core.LiteralsUtils.toInternal;

import org.sat4j.annotations.Feature;
import org.sat4j.core.VecInt;
import org.sat4j.specs.Constr;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.IteratorInt;

/**
 * Counter based implementation of the model minimization strategy to compute a
 * prime implicant. The main advantage of this method is to be linear in the
 * size (in number of literals) of the formula. It's main drawback is to be
 * limited to clauses (and cardinality constraints with some modifications). See
 * our FMCAD 2013 paper for details.
 * 
 * @author leberre
 * 
 */
@Feature(value = "primeimplicant", parent = "expert")
public class CounterBasedPrimeImplicantStrategy
        implements PrimeImplicantStrategy {

    private int[] prime;

    public int[] compute(Solver<? extends DataStructureFactory> solver) {
        long begin = System.currentTimeMillis();
        IVecInt[] watched = new IVecInt[solver.voc.nVars() * 2 + 2];
        for (int d : solver.fullmodel) {
            watched[toInternal(d)] = new VecInt();
        }
        int[] count = new int[solver.constrs.size()];
        Constr constr;
        IVecInt watch;
        for (int i = 0; i < solver.constrs.size(); i++) {
            constr = solver.constrs.get(i);
            if (!constr.canBeSatisfiedByCountingLiterals()) {
                throw new IllegalStateException(
                        "Algo2 does not work with constraints other than clauses and cardinalities"
                                + constr.getClass());
            }
            count[i] = 0;
            for (int j = 0; j < constr.size(); j++) {
                watch = watched[constr.get(j)];
                if (watch != null) {
                    // satisfied literal
                    watch.push(i);
                }
            }
        }
        for (int d : solver.fullmodel) {
            for (IteratorInt it = watched[toInternal(d)].iterator(); it
                    .hasNext();) {
                count[it.next()]++;
            }
        }
        this.prime = new int[solver.voc.nVars() + 1];
        int d;
        for (int i = 0; i < this.prime.length; i++) {
            this.prime[i] = 0;
        }
        for (IteratorInt it = solver.implied.iterator(); it.hasNext();) {
            d = it.next();
            this.prime[Math.abs(d)] = d;
        }
        int removed = 0;
        int posremoved = 0;
        int propagated = 0;
        int constrNumber;
        top: for (int i = 0; i < solver.decisions.size(); i++) {
            d = solver.decisions.get(i);
            for (IteratorInt it = watched[toInternal(d)].iterator(); it
                    .hasNext();) {
                constrNumber = it.next();
                if (count[constrNumber] == solver.constrs.get(constrNumber)
                        .requiredNumberOfSatisfiedLiterals()) {
                    this.prime[Math.abs(d)] = d;
                    propagated++;
                    continue top;
                }
            }
            removed++;
            if (d > 0 && d > solver.nVars()) {
                posremoved++;
            }
            for (IteratorInt it = watched[toInternal(d)].iterator(); it
                    .hasNext();) {
                count[it.next()]--;
            }
        }
        int[] implicant = new int[this.prime.length - removed - 1];
        int index = 0;
        for (int i : this.prime) {
            if (i != 0) {
                implicant[index++] = i;
            }
        }
        long end = System.currentTimeMillis();
        if (solver.isVerbose()) {
            System.out.printf(
                    "%s prime implicant computation statistics ALGO2%n",
                    solver.getLogPrefix());
            System.out.printf(
                    "%s implied: %d, decision: %d, removed %d (+%d), propagated %d, time(ms):%d %n",
                    solver.getLogPrefix(), solver.implied.size(),
                    solver.decisions.size(), removed, posremoved, propagated,
                    end - begin);
        }
        return implicant;
    }

    public int[] getPrimeImplicantAsArrayWithHoles() {
        if (prime == null) {
            throw new UnsupportedOperationException(
                    "Call the compute method first!");
        }
        return prime;
    }
}
