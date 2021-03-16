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
import java.util.Arrays;

import org.sat4j.specs.ISolver;

/**
 * ApproxMC implements the approximate model counter proposed by Chakraborty,
 * Meel and Vardi.
 * 
 * @author Romain WALLON
 */
public class ApproxMC2 extends AbstractApproxMC {

    /**
     * The number of cells that have been found.
     */
    private int nCells = 2;

    /**
     * Creates a new ApproxMC2.
     * 
     * @param solver
     *            The solver to use as an oracle.
     * @param epsilon
     *            The tolerance of the count.
     * @param delta
     *            the confidence of the count.
     */
    public ApproxMC2(ISolver solver, double epsilon, double delta) {
        super(solver, epsilon, delta);
    }

    /**
     * Creates a new ApproxMC2.
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
    public ApproxMC2(ISolver solver, SamplingSet samplingSet, double epsilon,
            double delta) {
        super(solver, samplingSet, epsilon, delta);
    }

    /**
     * Creates a new ApproxMC2.
     * 
     * @param solver
     *            The solver to use as an oracle.
     * @param samplingSet
     *            The set of variables to consider.
     */
    public ApproxMC2(ISolver solver, SamplingSet samplingSet) {
        super(solver, samplingSet);
    }

    /**
     * Creates a new ApproxMC2.
     * 
     * @param solver
     *            The solver to use as an oracle.
     */
    public ApproxMC2(ISolver solver) {
        super(solver);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.tools.counting.AbstractApproxMC#computeThreshold()
     */
    @Override
    protected int computeThreshold() {
        return (int) (1 + 9.84 * (1 + (epsilon / (1 + epsilon)))
                * (1 + 1 / epsilon) * (1 + 1 / epsilon));
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.tools.counting.AbstractApproxMC#computeIterCount()
     */
    @Override
    protected int computeIterCount() {
        return (int) (17 * Math.log(3 / delta) / Math.log(2));
    }

    /**
     * Counts an epsilon-approximate estimate of the model count of the
     * underlying formula, by partitioning the space of all the models into
     * "small" cells containing at most {@code pivot} models.
     * 
     * @param thresh
     *            The bound for the number of models in a cell.
     * 
     * @return The estimate of the model count, or {@code null} to report a
     *         counting error, i.e;, when all generated cells were either empty
     *         or too big.
     */
    @Override
    protected BigInteger internalCountModels(int thresh) {
        // Constraints are generated once and for all for this run.
        generator.generate(samplingSet.nVars());

        // Counting with all parity constraints.
        long count = boundedSAT(thresh);
        generator.deactivate();
        if (count >= thresh) {
            // Reporting a counting error.
            return null;
        }

        // This is equivalent to nConstrPrev = log2(nCells)
        int nConstrPrev = Integer.SIZE - Integer.numberOfLeadingZeros(nCells)
                - 1;

        // Computing the number of models with the optimal set of constraints.
        int nConstr = logSatSearch(thresh, nConstrPrev);
        BigInteger nSols = BigInteger.valueOf(boundedSAT(nConstr, thresh));

        // Forgetting all parity constraints used in this run.
        generator.clear();

        // The number of models needs to be scaled w.r.t. the number of cells.
        return nSols.shiftLeft(nConstr);
    }

    /**
     * Performs a logarithmic search for the optimal number of parity
     * constraints to consider.
     * 
     * @param thresh
     *            The maximum number of models to consider.
     * @param nConstrPrev
     *            The previous number of parity constraints that were added.
     * 
     * @return The best number of parity constraints to add.
     */
    private int logSatSearch(int thresh, int nConstrPrev) {
        int loIndex = 0;
        int hiIndex = samplingSet.nVars() - 1;
        int nConstr = nConstrPrev;
        int[] cells = new int[samplingSet.nVars()];
        Arrays.fill(cells, -1);
        cells[0] = 1;
        cells[samplingSet.nVars() - 1] = 0;

        for (;;) {
            long y = boundedSAT(nConstr, thresh);
            if (y >= thresh) {
                // There are too many constraints.
                if (cells[nConstr + 1] == 0) {
                    return nConstr + 1;
                }
                Arrays.fill(cells, 1, nConstr + 1, 1);
                loIndex = nConstr;
                if (Math.abs(nConstr - nConstrPrev) < 3) {
                    nConstr++;
                } else if ((nConstr << 1) < (samplingSet.nVars() - 1)) {
                    nConstr <<= 1;
                } else {
                    nConstr = (hiIndex + nConstr) >> 1;
                }

            } else {
                // There is enough constraints, but maybe too many.
                if (cells[nConstr - 1] == 1) {
                    return nConstr;
                }
                Arrays.fill(cells, nConstr, samplingSet.nVars(), 0);
                hiIndex = nConstr;
                if (Math.abs(nConstr - nConstrPrev) < 3) {
                    nConstr--;
                } else {
                    nConstr = (nConstr + loIndex) >> 1;
                }
            }
        }
    }

    /**
     * Counts up to {@code bound} models of the formula, after having added
     * {@code nbConstraints} parity constraints to the solver.
     * 
     * @param nbConstraints
     *            The number of constraints to add.
     * @param bound
     *            The maximum number of models to count.
     * 
     * @return The number of models that have been counted.
     */
    private long boundedSAT(int nbConstraints, int bound) {
        generator.activate(nbConstraints);
        long count = boundedSAT(bound);
        generator.deactivate(nbConstraints);
        return count;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.tools.counting.AbstractApproxMC#reset()
     */
    @Override
    public void reset() {
        this.nCells = 2;
    }

}
