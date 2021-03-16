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

import java.util.Set;
import java.util.TreeSet;

import org.sat4j.core.VecInt;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.IteratorInt;

/**
 * That class allows to iterate through all the models (implicants) of a
 * formula.
 * 
 * <pre>
 * IVecInt subsetVars = new VecInt();
 * ISolver solver = new SubModelIterator(SolverFactory.OneSolver(), subsetVars);
 * boolean unsat = true;
 * while (solver.isSatisfiable()) {
 *     unsat = false;
 *     int[] model = solver.model();
 *     // do something with the submodel
 * }
 * if (unsat) {
 *     // UNSAT case
 * }
 * </pre>
 * 
 * It is also possible to limit the number of models returned:
 * 
 * <pre>
 * ISolver solver = new OneModelIterator(SolverFactory.OneSolver(), subsetVars, 10);
 * </pre>
 * 
 * will return at most 10 submodels.
 * 
 * @author leberre
 * @since 2.3.6
 */
public class SubModelIterator extends ModelIterator {

    private static final long serialVersionUID = 1L;

    private final Set<Integer> subsetVars;

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
    public SubModelIterator(ISolver solver, IVecInt subsetVars) {
        this(solver, subsetVars, Long.MAX_VALUE);
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
     * @see #isSatisfiable()
     * @see #isSatisfiable(boolean)
     * @see #isSatisfiable(IVecInt)
     * @see #isSatisfiable(IVecInt, boolean)
     * @see #model()
     */
    public SubModelIterator(ISolver solver, IVecInt subsetVars, long bound) {
        super(solver, bound);
        this.subsetVars = new TreeSet<Integer>();
        for (IteratorInt it = subsetVars.iterator(); it.hasNext();) {
            this.subsetVars.add(it.next());
        }
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.ISolver#model()
     */
    @Override
    public int[] model() {
        int[] last = super.model();
        this.nbModelFound++;
        int[] sub = new int[subsetVars.size()];
        IVecInt clause = new VecInt(sub.length);
        int var;
        int i = 0;
        for (int q : last) {
            var = Math.abs(q);
            if (subsetVars.contains(var)) {
                clause.push(-q);
                sub[i++] = q;
            }
        }
        try {
            addBlockingClause(clause);
        } catch (ContradictionException e) {
            this.trivialfalsity = true;
        }
        return sub;
    }

    @Override
    public int[] primeImplicant() {
        throw new UnsupportedOperationException();
    }
}
