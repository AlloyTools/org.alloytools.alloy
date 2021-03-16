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

import org.sat4j.annotations.Feature;
import org.sat4j.core.ConstrGroup;
import org.sat4j.core.VecInt;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;

/**
 * That class allows to iterate through all the models (implicants) of a
 * formula.
 * 
 * <pre>
 * ISolver solver = new ModelIterator(SolverFactory.OneSolver());
 * boolean unsat = true;
 * while (solver.isSatisfiable()) {
 *     unsat = false;
 *     int[] model = solver.model();
 *     // do something with model
 * }
 * if (unsat) {
 *     // UNSAT case
 * }
 * </pre>
 * 
 * It is also possible to limit the number of models returned:
 * 
 * <pre>
 * ISolver solver = new ModelIterator(SolverFactory.OneSolver(), 10);
 * </pre>
 * 
 * will return at most 10 models.
 * 
 * @author leberre
 */
@Feature("solver")
public class ModelIterator extends SolverDecorator<ISolver> {

    private static final long serialVersionUID = 1L;

    protected boolean trivialfalsity = false;
    private long bound;
    protected long nbModelFound = 0;

    private final ConstrGroup blockingClauses = new ConstrGroup();

    /**
     * Create an iterator over the solutions available in <code>solver</code>.
     * The iterator will look for one new model at each call to isSatisfiable()
     * and will discard that model at each call to model().
     * 
     * @param solver
     *            a solver containing the constraints to satisfy.
     * @see #isSatisfiable()
     * @see #isSatisfiable(boolean)
     * @see #isSatisfiable(IVecInt)
     * @see #isSatisfiable(IVecInt, boolean)
     * @see #model()
     */
    public ModelIterator(ISolver solver) {
        this(solver, Long.MAX_VALUE);
    }

    /**
     * Create an iterator over a limited number of solutions available in
     * <code>solver</code>. The iterator will look for one new model at each
     * call to isSatisfiable() and will discard that model at each call to
     * model(). At most <code>bound</code> calls to models() will be allowed
     * before the method <code>isSatisfiable()</code> returns false.
     * 
     * @param solver
     *            a solver containing the constraints to satisfy.
     * @param bound
     *            the maximum number of models to return.
     * @since 2.1
     * @see #isSatisfiable()
     * @see #isSatisfiable(boolean)
     * @see #isSatisfiable(IVecInt)
     * @see #isSatisfiable(IVecInt, boolean)
     * @see #model()
     */
    public ModelIterator(ISolver solver, long bound) {
        super(solver);
        this.bound = bound;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.ISolver#model()
     */
    @Override
    public int[] model() {
        int[] last = super.model();
        this.nbModelFound += 1 << (nVars() - last.length);
        try {
            blockingClauses.add(discardCurrentModel());
        } catch (ContradictionException e) {
            this.trivialfalsity = true;
        }
        return last;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.ISolver#isSatisfiable()
     */
    @Override
    public boolean isSatisfiable() throws TimeoutException {
        if (this.trivialfalsity || this.nbModelFound >= this.bound) {
            expireTimeout();
            return false;
        }
        this.trivialfalsity = false;
        return super.isSatisfiable(true);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.ISolver#isSatisfiable(org.sat4j.datatype.VecInt)
     */
    @Override
    public boolean isSatisfiable(IVecInt assumps) throws TimeoutException {
        if (this.trivialfalsity || this.nbModelFound >= this.bound) {
            return false;
        }
        this.trivialfalsity = false;
        return super.isSatisfiable(assumps, true);
    }

    @Override
    public boolean isSatisfiable(boolean global) throws TimeoutException {
        return isSatisfiable();
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.ISolver#reset()
     */
    @Override
    public void reset() {
        this.trivialfalsity = false;
        this.nbModelFound = 0;
        super.reset();
    }

    @Override
    public int[] primeImplicant() {
        int[] last = super.primeImplicant();
        this.nbModelFound += Math.pow(2, nVars() - last.length);
        IVecInt clause = new VecInt(last.length);
        for (int q : last) {
            clause.push(-q);
        }
        try {
            blockingClauses.add(addBlockingClause(clause));
        } catch (ContradictionException e) {
            this.trivialfalsity = true;
        }
        return last;
    }

    /**
     * To know the number of models already found.
     * 
     * @return the number of models found so far.
     * @since 2.3
     */
    public long numberOfModelsFoundSoFar() {
        return this.nbModelFound;
    }

    /**
     * Clear blocking clauses
     * 
     * @since 2.3.6
     */
    public void clearBlockingClauses() {
        this.trivialfalsity = false;
        this.nbModelFound = 0;
        blockingClauses.removeFrom(this);
        blockingClauses.clear();
    }

    /**
     * Return the maximum number of models to enumerate.
     * 
     * @return the current bound
     * @since 2.3.6
     */
    public long getBound() {
        return bound;
    }

    /**
     * Change the maximum number of models to enumerate.
     * 
     * @param bound
     *            the new bound.
     * @since 2.3.6
     */
    public void setBound(long bound) {
        this.bound = bound;
    }
}
