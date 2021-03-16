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
import java.util.Comparator;

import org.sat4j.core.Vec;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVec;

/**
 * The AbstractApproxMC defines the base structure for the various
 * implementations of the ApproxMC algorithm proposed by Chakraborty, Meel and
 * Vardi.
 * 
 * @author Romain Wallon
 */
public abstract class AbstractApproxMC implements IModelCounter {

    /**
     * The default EPSILON value (tolerance) to use as parameter for the
     * algorithm.
     */
    public static final double DEFAULT_EPSILON = .1;

    /**
     * The default DELTA value (confidence) to use as parameter for the
     * algorithm.
     */
    public static final double DEFAULT_DELTA = .1;

    /**
     * The EPSILON parameter for the algorithm, i.e. the tolerance of the count.
     */
    protected final double epsilon;

    /**
     * The DELTA parameter for the algorithm, i.e. the confidence of the count.
     */
    protected final double delta;

    /**
     * The set of variables to consider when creating parity constraints.
     */
    protected final SamplingSet samplingSet;

    /**
     * The generator for the parity constraints to add to the solver.
     */
    protected final ParityConstraintGenerator generator;

    /**
     * The model counter used to exactly count the models of the randomly
     * modified formulas.
     */
    private final ModelCounterAdapter counter;

    /**
     * Creates a new AbstractApproxMC.
     * 
     * @param solver
     *            The solver to use as an oracle.
     */
    protected AbstractApproxMC(ISolver solver) {
        this(solver, AllVariablesSamplingSet.of(solver));
    }

    /**
     * Creates a new AbstractApproxMC.
     * 
     * @param solver
     *            The solver to use as an oracle.
     * @param samplingSet
     *            The set of variables to consider.
     */
    protected AbstractApproxMC(ISolver solver, SamplingSet samplingSet) {
        this(solver, samplingSet, DEFAULT_EPSILON, DEFAULT_DELTA);
    }

    /**
     * Creates a new AbstractApproxMC.
     * 
     * @param solver
     *            The solver to use as an oracle.
     * @param epsilon
     *            The tolerance of the count.
     * @param delta
     *            the confidence of the count.
     */
    protected AbstractApproxMC(ISolver solver, double epsilon, double delta) {
        this(solver, AllVariablesSamplingSet.of(solver), epsilon, delta);
    }

    /**
     * Creates a new AbstractApproxMC.
     * 
     * @param solver
     *            The solver to use as an oracle.
     * @param samplingSet
     *            The set of variables to consider.
     * @param epsilon
     *            The tolerance of the count.
     * @param delta
     *            the confidence of the count.
     */
    protected AbstractApproxMC(ISolver solver, SamplingSet samplingSet,
            double epsilon, double delta) {
        this.counter = ModelCounterAdapter.newInstance(solver);
        this.epsilon = epsilon;
        this.delta = delta;
        this.samplingSet = samplingSet;
        this.generator = new ParityConstraintGenerator(solver, samplingSet);
    }

    /**
     * Counts an approximation {@code m} of the number of models of the
     * underlying formula {@code F}. This number verifies
     * {@code (#F / (1 + epsilon) <= m <= (1 + epsilon) #F)} with probability
     * {@code (1 - delta)}.
     * 
     * This is a template method, which invokes multiple times
     * {@link #internalCountModels(int)} so as to get several approximations.
     * 
     * @return An approximate count of the number of solutions.
     * 
     * @see #internalCountModels(int)
     */
    @Override
    public final BigInteger countModels() {
        // Trying to compute exactly the number of models.
        int threshold = computeThreshold();
        long initialCount = boundedSAT(threshold);
        if (initialCount < threshold) {
            return BigInteger.valueOf(initialCount);
        }

        // Computing the number of models for t random formulas.
        int iterCount = computeIterCount();
        IVec<BigInteger> counts = new Vec<BigInteger>(iterCount);
        for (int i = 0; i < iterCount; i++) {
            BigInteger count = internalCountModels(threshold);
            if (count != null) {
                counts.push(count);
            }
        }

        // The approximate count is the median of all counts.
        return findMedian(counts);
    }

    /**
     * Computes the threshold to apply w.r.t. the tolerance wanted for the
     * algorithm.
     * 
     * @return The bound for the number of models to find when invoking the
     *         (bounded) SAT oracle.
     * 
     * @see #boundedSAT(int)
     */
    protected abstract int computeThreshold();

    /**
     * Computes the number of approximations to make so as to get a number of
     * models that is, with high probability, close to the real number of
     * models.
     * 
     * @return The number of iterations to perform.
     */
    protected abstract int computeIterCount();

    /**
     * Counts an epsilon-approximate estimate of the model count of the
     * underlying formula, by partitioning the space of all the models into
     * "small" cells containing at most {@code threshold} models.
     * 
     * @param threshold
     *            The bound for the number of models in a cell.
     * 
     * @return The estimate of the model count, or {@code null} to report a
     *         counting error, i.e;, when all generated cells were either empty
     *         or too big.
     */
    protected abstract BigInteger internalCountModels(int threshold);

    /**
     * Counts up to {@code bound} models of the current formula, by enumerating
     * these models.
     * 
     * @param bound
     *            The maximum number of models to count.
     * 
     * @return The number of models that have been found.
     */
    protected final long boundedSAT(int bound) {
        counter.setBound(bound);
        BigInteger foundModels = counter.countModels();
        counter.reset();
        return foundModels.longValue();
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.tools.counting.IModelCounter#reset()
     */
    @Override
    public void reset() {
        // Nothing to do by default.
    }

    /**
     * Computes the median of a vector of values.
     * 
     * @param values
     *            The values to compute the median of.
     * 
     * @return The median of the vector of values, or {@link BigInteger#ZERO} if
     *         the vector is empty (which, in the case of model counting, means
     *         that the formula is unsatisfiable).
     */
    private static BigInteger findMedian(IVec<BigInteger> values) {
        if (values.isEmpty()) {
            return BigInteger.ZERO;
        }

        // The values need to be sorted to find the median...
        values.sort(new Comparator<BigInteger>() {
            @Override
            public int compare(BigInteger o1, BigInteger o2) {
                return o1.compareTo(o2);
            }
        });

        // ... which is at the middle-th position of the vector.
        return values.get(values.size() >> 1);
    }

}
