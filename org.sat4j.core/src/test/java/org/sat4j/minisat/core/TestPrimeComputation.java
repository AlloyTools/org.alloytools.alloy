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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.util.Arrays;
import java.util.Collection;

import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.minisat.orders.PositiveLiteralSelectionStrategy;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;

@RunWith(value = Parameterized.class)
public class TestPrimeComputation {

    private Solver<DataStructureFactory> solver;
    private final PrimeImplicantStrategy prime;

    public TestPrimeComputation(PrimeImplicantStrategy prime) {
        this.prime = prime;
    }

    @Parameters
    public static Collection<Object[]> strategies() {
        return Arrays.asList(new Object[][] {
                { new QuadraticPrimeImplicantStrategy() },
                { new CounterBasedPrimeImplicantStrategy() },
                { new WatcherBasedPrimeImplicantStrategy() } });
    }

    @Before
    public void setUp() {
        this.solver = SolverFactory.newBestWL();
        this.solver.getOrder().setPhaseSelectionStrategy(
                new PositiveLiteralSelectionStrategy());
    }

    @Test
    public void testBasicImplicant() throws ContradictionException,
            TimeoutException {
        IVecInt clause = new VecInt();
        clause.push(1).push(-2).push(3);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(-1).push(2).push(3);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(1).push(2).push(-3);
        this.solver.addClause(clause);
        clause.clear();
        assertTrue(this.solver.isSatisfiable());
        int[] model = this.solver.model();
        assertEquals(3, model.length);
        int[] implicant = prime.compute(solver);
        assertEquals(2, implicant.length);
    }

    @Test
    public void testImplicantPascal() throws ContradictionException,
            TimeoutException {
        IVecInt clause = new VecInt();
        clause.push(1).push(-2).push(3).push(-4);
        this.solver.addClause(clause);
        assertTrue(this.solver.isSatisfiable());
        int[] model = this.solver.model();
        assertEquals(4, model.length);
        int[] implicant = prime.compute(solver);
        assertEquals(1, implicant.length);
    }

    @Test
    public void testOtherImplicant() throws ContradictionException,
            TimeoutException {
        IVecInt clause = new VecInt();
        clause.push(1).push(-2).push(3);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(1).push(2).push(3);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(1).push(2).push(-3);
        this.solver.addClause(clause);
        clause.clear();
        assertTrue(this.solver.isSatisfiable());
        int[] model = this.solver.model();
        assertEquals(3, model.length);
        int[] implicant = prime.compute(solver);
        assertEquals(2, implicant.length);
        clause.push(1).push(-2).push(-3);
        this.solver.addBlockingClause(clause);
        assertTrue(this.solver.isSatisfiable());
        clause.clear();
        model = this.solver.model();
        assertEquals(3, model.length);
        implicant = prime.compute(solver);
        assertEquals(1, implicant.length);
    }

    @Test
    public void testFolletExample() throws ContradictionException,
            TimeoutException {
        IVecInt clause = new VecInt();
        clause.push(1);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(2).push(3);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(3);
        this.solver.addClause(clause);
        clause.clear();
        assertTrue(this.solver.isSatisfiable());
        int[] model = this.solver.model();
        assertEquals(3, model.length);
        int[] implicant = prime.compute(solver);
        assertEquals(2, implicant.length);
    }
}
