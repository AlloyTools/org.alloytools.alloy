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
package org.sat4j.tools;

import java.util.BitSet;

import org.sat4j.core.VecInt;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IConstr;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.IteratorInt;
import org.sat4j.specs.TimeoutException;

/**
 * The aim of this class is to compute efficiently the literals implied by the
 * set of constraints (also called backbone or unit implicates).
 * 
 * The work has been done in the context of ANR BR4CP.
 * 
 * @author leberre
 * 
 */
public final class Backbone {

    abstract static class Backboner {
        protected IBackboneProgressListener listener = IBackboneProgressListener.VOID;
        protected int nbSatTests;
        private boolean implicant = true;

        public void setBackboneProgressListener(
                IBackboneProgressListener listener) {
            this.listener = listener;
        }

        public void setImplicantSimplification(boolean b) {
            this.implicant = b;
        }

        public int[] simplifiedModel(ISolver solver) {
            if (implicant) {
                return solver.primeImplicant();
            }
            return solver.model();
        }

        public IVecInt compute(ISolver solver, int[] implicant,
                IVecInt assumptions) throws TimeoutException {
            nbSatTests = 0;
            BitSet assumptionsSet = new BitSet(solver.nVars());
            for (IteratorInt it = assumptions.iterator(); it.hasNext();) {
                assumptionsSet.set(Math.abs(it.next()));
            }
            IVecInt litsToTest = new VecInt();
            for (int p : implicant) {
                if (!assumptionsSet.get(Math.abs(p))) {
                    litsToTest.push(-p);
                }
            }
            return compute(solver, assumptions, litsToTest);
        }

        public int nbSatTests() {
            return this.nbSatTests;
        }

        void incSatTests() {
            nbSatTests++;
        }

        public IVecInt compute(ISolver solver, int[] implicant,
                IVecInt assumptions, IVecInt filter) throws TimeoutException {
            nbSatTests = 0;
            BitSet assumptionsSet = new BitSet(solver.nVars());
            for (IteratorInt it = assumptions.iterator(); it.hasNext();) {
                assumptionsSet.set(Math.abs(it.next()));
            }
            BitSet filterSet = new BitSet();
            for (IteratorInt it = filter.iterator(); it.hasNext();) {
                filterSet.set(Math.abs(it.next()));
            }
            IVecInt litsToTest = new VecInt();
            for (int p : implicant) {
                if (!assumptionsSet.get(Math.abs(p))
                        && filterSet.get(Math.abs(p))) {
                    litsToTest.push(-p);
                }
            }
            return compute(solver, assumptions, litsToTest);
        }

        abstract IVecInt compute(ISolver solver, IVecInt assumptions,
                IVecInt litsToTest) throws TimeoutException;

        static void removeVarNotPresentAndSatisfiedLits(int[] implicant,
                IVecInt litsToTest, int n) {
            int[] marks = new int[n + 1];
            for (int p : implicant) {
                marks[p > 0 ? p : -p] = p;
            }
            int q, mark;
            for (int i = 0; i < litsToTest.size();) {
                q = litsToTest.get(i);
                mark = marks[q > 0 ? q : -q];
                if (mark == 0 || mark == q) {
                    litsToTest.delete(i);
                } else {
                    i++;
                }
            }
        }
    }

    /**
     * Computes the backbone of a formula following the iterative algorithm
     * described in Joao Marques-Silva, Mikolas Janota, Ines Lynce: On Computing
     * Backbones of Propositional Theories. ECAI 2010: 15-20 and using Sat4j
     * specific prime implicant computation.
     * 
     */
    private static final Backboner BB = new Backboner() {

        @Override
        IVecInt compute(ISolver solver, IVecInt assumptions, IVecInt litsToTest)
                throws TimeoutException {
            int[] implicant;
            IVecInt candidates = new VecInt();
            assumptions.copyTo(candidates);
            int p;
            int initLitsToTestSize = litsToTest.size();
            listener.start(initLitsToTestSize);
            while (!litsToTest.isEmpty()) {
                listener.inProgress(initLitsToTestSize - litsToTest.size(),
                        initLitsToTestSize);
                p = litsToTest.last();
                candidates.push(p);
                litsToTest.pop();
                if (solver.isSatisfiable(candidates)) {
                    candidates.pop();
                    implicant = simplifiedModel(solver);
                    removeVarNotPresentAndSatisfiedLits(implicant, litsToTest,
                            solver.nVars());
                } else {
                    candidates.pop().push(-p);
                }
                incSatTests();
            }
            listener.end(nbSatTests);
            return candidates;
        }
    };

    /**
     * Computes the backbone of a formula using the iterative approach found in
     * BB but testing a set of literals at once instead of only one. This
     * approach outperforms BB in terms of SAT calls. Both approaches are made
     * available for testing purposes.
     * 
     */
    private static final Backboner IBB = new Backboner() {

        @Override
        IVecInt compute(ISolver solver, IVecInt assumptions, IVecInt litsToTest)
                throws TimeoutException {
            int[] implicant;
            IVecInt candidates = new VecInt();
            assumptions.copyTo(candidates);
            IConstr constr;
            int initLitsToTestSize = litsToTest.size();
            listener.start(initLitsToTestSize);
            while (!litsToTest.isEmpty()) {
                listener.inProgress(initLitsToTestSize - litsToTest.size(),
                        initLitsToTestSize);
                try {
                    constr = solver.addBlockingClause(litsToTest);
                    if (solver.isSatisfiable(candidates)) {
                        implicant = simplifiedModel(solver);
                        removeVarNotPresentAndSatisfiedLits(implicant,
                                litsToTest, solver.nVars());
                    } else {
                        for (IteratorInt it = litsToTest.iterator(); it
                                .hasNext();) {
                            candidates.push(-it.next());
                        }
                        litsToTest.clear();
                    }
                    solver.removeSubsumedConstr(constr);
                } catch (ContradictionException e) {
                    for (IteratorInt it = litsToTest.iterator(); it
                            .hasNext();) {
                        candidates.push(-it.next());
                    }
                    litsToTest.clear();
                }
                incSatTests();
            }
            listener.end(nbSatTests);
            solver.clearLearntClauses();
            return candidates;
        }
    };

    private final Backboner bb;

    private final static Backbone instance = bb();

    private Backbone(Backboner bb) {
        this.bb = bb;
    }

    public static Backbone instance() {
        return instance;
    }

    public static Backbone instance(IBackboneProgressListener listener,
            boolean primeImplicantSimplification) {
        instance.bb.setBackboneProgressListener(listener);
        instance.bb.setImplicantSimplification(primeImplicantSimplification);
        return instance;
    }

    public static Backbone bb() {
        return new Backbone(BB);
    }

    public static Backbone ibb() {
        return new Backbone(IBB);
    }

    public IVecInt compute(ISolver solver) throws TimeoutException {
        return compute(solver, VecInt.EMPTY);
    }

    /**
     * Computes the backbone of a formula.
     * 
     * 
     * @param solver
     *            a solver containing a satisfiable set of constraints.
     * @param assumptions
     *            a set of literals to satisfy
     * @return the backbone of the solver when the assumptions are satisfied
     * @throws TimeoutException
     *             if the computation cannot be done within the timeout
     * @throws IllegalArgumentException
     *             if solver is unsatisfiable
     */
    public IVecInt compute(ISolver solver, IVecInt assumptions)
            throws TimeoutException {
        boolean result = solver.isSatisfiable(assumptions);
        if (!result) {
            throw new IllegalArgumentException("Formula is UNSAT!");
        }
        return bb.compute(solver, solver.primeImplicant(), assumptions);

    }

    /**
     * Computes the backbone of a formula.
     * 
     * 
     * @param solver
     *            a solver containing a satisfiable set of constraints.
     * @param assumptions
     *            a set of literals to satisfy
     * @param filter
     *            a set of variables
     * @return the backbone of the solver restricted to the variables of filter
     *         when the assumptions are satisfied
     * @throws TimeoutException
     *             if the computation cannot be done within the timeout
     * @throws IllegalArgumentException
     *             if solver is unsatisfiable
     */
    public IVecInt compute(ISolver solver, IVecInt assumptions, IVecInt filter)
            throws TimeoutException {
        boolean result = solver.isSatisfiable(assumptions);
        if (!result) {
            throw new IllegalArgumentException("Formula is UNSAT!");
        }
        return bb.compute(solver, solver.primeImplicant(), assumptions, filter);

    }

    /**
     * Computes the backbone of a formula.
     * 
     * 
     * @param solver
     *            a solver containing a satisfiable set of constraints.
     * @param implicant
     *            an implicant of solver
     * @return the backbone of the solver
     * @throws TimeoutException
     *             if the computation cannot be done within the timeout
     */
    public IVecInt compute(ISolver solver, int[] implicant)
            throws TimeoutException {
        return bb.compute(solver, implicant, VecInt.EMPTY);
    }

    /**
     * Computes the backbone of a formula.
     * 
     * 
     * @param solver
     *            a solver containing a satisfiable set of constraints.
     * @param implicant
     *            an implicant of solver
     * @param assumptions
     *            a set of literals to satisfy
     * @return the backbone of the solver when the assumptions are satisfied
     * @throws TimeoutException
     *             if the computation cannot be done within the timeout
     */
    public IVecInt compute(ISolver solver, int[] implicant, IVecInt assumptions)
            throws TimeoutException {
        return bb.compute(solver, implicant, assumptions);
    }

    /**
     * Returns the number of calls to the SAT solver needed to compute the
     * backbone.
     * 
     * @return the number of underlying calls to the SAT solver.
     */
    public int getNumberOfSatCalls() {
        return bb.nbSatTests();
    }
}
