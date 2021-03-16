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

import static org.junit.Assert.assertTrue;

import java.io.IOException;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Arrays;
import java.util.Collection;

import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.reader.DimacsReader;
import org.sat4j.reader.ParseFormatException;
import org.sat4j.reader.Reader;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;

/**
 * Base class for the test cases checking that the various implementations of
 * ApproxMC find a number of models that is, with high probability, close to the
 * real number of models of a formula.
 * 
 * @author Romain WALLON
 */
@RunWith(Parameterized.class)
public abstract class AbstractApproxMCTest {

    /**
     * The tolerance to use for the tests.
     */
    protected static final double EPSILON_TEST = .5;

    /**
     * The confidence to use for the tests.
     */
    protected static final double DELTA_TEST = .5;

    /**
     * The number of times to execute the model counter so as to evaluate its
     * probabilistic behavior.
     */
    private static final int NUMBER_OF_TRIES = 20;

    /**
     * The number of times the counter is expected to find a good approximation.
     */
    private static final int EXPECTED = (int) (NUMBER_OF_TRIES
            * (1 - ApproxMC.DEFAULT_DELTA));

    /**
     * The name of the benchmark on which to test the counter.
     */
    private final String benchmark;

    /**
     * The real number of models of the instance.
     */
    private final BigInteger realCount;

    /**
     * The solver used as an oracle by the model counter.
     */
    protected ISolver solver;

    /**
     * Creates a new ApproxMC test case.
     * 
     * @param benchmark
     *            The name of the benchmark on which to test the counter.
     * @param realCount
     *            The real number of models of the input.
     */
    public AbstractApproxMCTest(String benchmark, BigInteger realCount) {
        this.benchmark = benchmark;
        this.realCount = realCount;
    }

    /**
     * Gives an array containing the benchmarks on which to test the model
     * counter, and the real number of models.
     * 
     * @return The test parameters.
     */
    @Parameters
    public static Collection<Object[]> benchmarks() {
        return Arrays.asList(new Object[][] {
                { "blockmap_05_01.net.cnf", BigInteger.valueOf(640) },
                { "jnh/jnh12.cnf", BigInteger.valueOf(80) },
                { "jnh/jnh17.cnf", BigInteger.valueOf(513) },
                { "jnh/jnh213.cnf", BigInteger.valueOf(4264) },
                { "jnh/jnh1.cnf", BigInteger.valueOf(11711) },
                { "jnh/jnh218.cnf", BigInteger.valueOf(14082) } });
    }

    /**
     * Initializes the solver to use as an oracle before executing the tests.
     * 
     * @throws IOException
     *             If the file could not be opened.
     * @throws ParseFormatException
     *             If the format of the input is incorrect.
     * @throws ContradictionException
     *             If the instance is trivially unsatisfiable.
     * 
     */
    @Before
    public void setUp()
            throws IOException, ContradictionException, ParseFormatException {
        solver = SolverFactory.newDefault();
        Reader reader = new DimacsReader(solver);
        reader.parseInstance("src/test/testfiles/" + benchmark);
    }

    /**
     * Test method for
     * {@link org.sat4j.tools.counting.ApproxMC#countSolutions()}.
     */
    @Test
    public void testCountSolutions() {
        int nbCorrect = checkModelCount();
        assertTrue(nbCorrect + " < " + EXPECTED, nbCorrect >= EXPECTED);
    }

    /**
     * Checks that the estimated count is within the theoretical bounds with
     * high probability on the given input.
     * 
     * @param solver
     *            The input solver.
     * @param realCount
     *            The real count of models.
     * 
     * @return The number of times the counter has found a good approximation.
     */
    private int checkModelCount() {
        // The theoretical lower bound for the confidence interval.
        BigDecimal lower = new BigDecimal(realCount)
                .multiply(BigDecimal.valueOf(1 / (1 + EPSILON_TEST)));

        // The theoretical upper bound for the confidence interval.
        BigDecimal upper = new BigDecimal(realCount)
                .multiply(BigDecimal.valueOf(1 + EPSILON_TEST));

        // Counting the models.
        int nbInExpectedBounds = 0;
        AbstractApproxMC counter = createCounter();
        for (int i = 0; i < NUMBER_OF_TRIES; i++) {
            BigDecimal nbSolutions = new BigDecimal(counter.countModels());
            if (lower.compareTo(nbSolutions) <= 0
                    && nbSolutions.compareTo(upper) <= 0) {
                // The estimate count is within the theoretical bounds.
                nbInExpectedBounds++;
            }
        }

        // To be correct, we need to find a count within the bounds matching the
        // expected probability.
        return nbInExpectedBounds;
    }

    /**
     * Creates the counter to test.
     * 
     * @return The counter to test.
     */
    protected abstract AbstractApproxMC createCounter();

}
