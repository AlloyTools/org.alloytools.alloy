/*******************************************************************************
 * SAT4J: a SATisfiability library for Java Copyright (C) 2004, 2019 Artois University and CNRS
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

package org.sat4j.tools.counting;

import java.math.BigInteger;

import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;
import org.sat4j.tools.ModelIteratorToSATAdapter;
import org.sat4j.tools.SolutionFoundListener;

/**
 * This class is an object adapter allowing to count the models of a formula by
 * iterating over its models.
 * 
 * As such, this model counter is <b>really slow</b>, and should only be used
 * either on small formulas or with a low bound. Use it with caution!
 * 
 * @author Romain Wallon
 */
public final class ModelCounterAdapter implements IModelCounter {

    /**
     * The adapted model iterator.
     */
    private final ModelIteratorToSATAdapter adaptee;

    /**
     * Creates a new ModelCounterAdapter.
     * 
     * @param solver
     *            The solver to adapt.
     */
    private ModelCounterAdapter(ISolver solver) {
        this.adaptee = new ModelIteratorToSATAdapter(solver,
                SolutionFoundListener.VOID);
    }

    /**
     * Creates a new ModelCounterAdapter adapting the given solver. The number
     * of models to count is not upper bounded.
     * 
     * @param solver
     *            The solver to adapt.
     * 
     * @return The created model counter.
     */
    public static ModelCounterAdapter newInstance(ISolver solver) {
        return newInstance(solver, Long.MAX_VALUE);
    }

    /**
     * Creates a new ModelCounterAdapter adapting the given solver.
     * 
     * @param solver
     *            The solver to adapt.
     * @param bound
     *            The maximum number of models to count.
     * 
     * @return The created model counter.
     */
    public static ModelCounterAdapter newInstance(ISolver solver, long bound) {
        ModelCounterAdapter counter = new ModelCounterAdapter(solver);
        counter.setBound(bound);
        return counter;
    }

    /**
     * Counts the models of the given solver. This method is designed for
     * convenience, so as to avoid manipulating instances of
     * {@link ModelCounterAdapter} if only one call is needed.
     * 
     * @param solver
     *            The solver to count the models of.
     * 
     * @return The number of models of the given solver.
     */
    public static BigInteger countModels(ISolver solver) {
        return countModels(solver, Long.MAX_VALUE);
    }

    /**
     * Counts up to {@code bound} models of the given solver. This is method is
     * designed for convenience, so as to avoid manipulating instances of
     * {@link ModelCounterAdapter} if only one call is needed.
     * 
     * @param solver
     *            The solver to count the models of.
     * @param bound
     *            The maximum number of models to count.
     * 
     * @return The number of models of the given solver.
     */
    public static BigInteger countModels(ISolver solver, long bound) {
        IModelCounter counter = newInstance(solver, bound);
        BigInteger nbModels = counter.countModels();
        counter.reset();
        return nbModels;
    }

    /**
     * Sets the bound for the number of models to count. A {@code long} will
     * always be sufficient, since counting each model one by one will never
     * allow to overflow a {@code long}.
     * 
     * @param bound
     *            The maximum number of models to count.
     */
    public void setBound(long bound) {
        adaptee.setBound(bound);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.tools.counting.IModelCounter#countModels()
     */
    @Override
    public BigInteger countModels() {
        try {
            // Calling this method will actually iterate over the models.
            adaptee.isSatisfiable();

        } catch (TimeoutException e) {
            // This exception is ignored.
            // We simply consider the number of models found so far.
        }

        return BigInteger.valueOf(adaptee.numberOfModelsFoundSoFar());
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.tools.counting.IModelCounter#reset()
     */
    @Override
    public void reset() {
        adaptee.clearBlockingClauses();
    }

}
