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

import static org.junit.Assert.assertEquals;

import java.util.List;

import org.junit.Before;
import org.junit.Test;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IConstr;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;

public class TestAllMUSes {

    private AllMUSes allMUSes;
    private ISolver solver;

    @Before
    public void setUp() throws Exception {
        this.allMUSes = new AllMUSes(SolverFactory.instance());
        this.solver = allMUSes.getSolverInstance();
    }

    @Test
    public void testSimpleCase() {
        IVecInt c1 = new VecInt();
        IVecInt c2 = new VecInt();
        IVecInt c3 = new VecInt();
        IVecInt c4 = new VecInt();
        IVecInt c5 = new VecInt();

        c1.push(1);
        c2.push(2);
        c3.push(-1).push(-2);
        c4.push(3);
        c5.push(-3);

        this.solver.newVar(3);

        try {
            this.solver.addClause(c1);
            this.solver.addClause(c2);
            this.solver.addClause(c3);
            this.solver.addClause(c4);
            this.solver.addClause(c5);

            List<IVecInt> muses = allMUSes.computeAllMUSes();

            assertEquals(muses.size(), 2);

        } catch (ContradictionException e) {
            e.printStackTrace();
        }

    }

    @Test
    public void testVerySimpleCase() {
        IVecInt c1 = new VecInt();
        IVecInt c2 = new VecInt();

        c1.push(1);
        c2.push(-1);

        this.solver.newVar(1);

        try {
            this.solver.addClause(c1);
            this.solver.addClause(c2);

            List<IVecInt> muses = allMUSes.computeAllMUSes();

            assertEquals(muses.size(), 1);

        } catch (ContradictionException e) {
            e.printStackTrace();
        }
    }

    @Test
    public void testGlobalInconsistency() throws ContradictionException,
            TimeoutException {
        this.solver.newVar(2);
        IVecInt clause = new VecInt();
        clause.push(1).push(2);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(1).push(-2);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(-1).push(2);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(-1).push(-2);
        this.solver.addClause(clause);
        clause.clear();
        List<IVecInt> muses = allMUSes.computeAllMUSes();
        assertEquals(1, muses.size());
    }

    @Test
    public void testGlobalInconsistencyIndex() throws ContradictionException,
            TimeoutException {
        this.solver.newVar(2);
        IVecInt clause = new VecInt();
        clause.push(1).push(2);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(1).push(-2);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(-1).push(2);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(-1).push(-2);
        this.solver.addClause(clause);
        clause.clear();
        List<IVecInt> muses = allMUSes.computeAllMUSes();
        assertEquals(1, muses.size());
    }

    @Test
    public void testAlmostGlobalInconsistency() throws ContradictionException,
            TimeoutException {
        this.solver.newVar(3);
        IVecInt clause = new VecInt();
        clause.push(1).push(2);
        IConstr c1 = this.solver.addClause(clause);
        clause.clear();
        clause.push(1).push(-2);
        IConstr c2 = this.solver.addClause(clause);
        clause.clear();
        clause.push(-1).push(2);
        IConstr c3 = this.solver.addClause(clause);
        clause.clear();
        clause.push(-1).push(-2);
        IConstr c4 = this.solver.addClause(clause);
        clause.clear();
        clause.push(1).push(3);
        this.solver.addClause(clause);
        clause.clear();
        List<IVecInt> muses = allMUSes.computeAllMUSes();
        assertEquals(1, muses.size());
    }

    @Test
    public void testAlmostGlobalInconsistencyIndex()
            throws ContradictionException, TimeoutException {
        this.solver.newVar(3);
        IVecInt clause = new VecInt();
        clause.push(1).push(2);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(1).push(-2);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(-1).push(2);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(-1).push(-2);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(1).push(3);
        this.solver.addClause(clause);
        clause.clear();
        List<IVecInt> muses = allMUSes.computeAllMUSes();
        assertEquals(1, muses.size());
    }

    @Test
    public void testAlmostGlobalInconsistencyII()
            throws ContradictionException, TimeoutException {
        this.solver.newVar(3);
        IVecInt clause = new VecInt();
        clause.push(1).push(2);
        IConstr c1 = this.solver.addClause(clause);
        clause.clear();
        clause.push(1).push(-2);
        IConstr c2 = this.solver.addClause(clause);
        clause.clear();
        clause.push(1).push(3);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(-1).push(2);
        IConstr c4 = this.solver.addClause(clause);
        clause.clear();
        clause.push(-1).push(-2);
        IConstr c5 = this.solver.addClause(clause);
        clause.clear();
        List<IVecInt> muses = allMUSes.computeAllMUSes();
        assertEquals(1, muses.size());

    }

    @Test
    public void testAlmostGlobalInconsistencyIIIndex()
            throws ContradictionException, TimeoutException {
        this.solver.newVar(3);
        IVecInt clause = new VecInt();
        clause.push(1).push(2);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(1).push(-2);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(1).push(3);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(-1).push(2);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(-1).push(-2);
        this.solver.addClause(clause);
        clause.clear();
        List<IVecInt> muses = allMUSes.computeAllMUSes();
        assertEquals(1, muses.size());
    }

    @Test
    public void testTheCaseOfTwoMUSes() throws ContradictionException,
            TimeoutException {
        this.solver.newVar(4);
        IVecInt clause = new VecInt();
        clause.push(1).push(2);
        IConstr c1 = this.solver.addClause(clause);
        clause.clear();
        clause.push(1).push(-2);
        IConstr c2 = this.solver.addClause(clause);
        clause.clear();
        clause.push(-1).push(3);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(-1).push(-3);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(-1).push(4);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(-1).push(-4);
        this.solver.addClause(clause);
        clause.clear();
        List<IVecInt> muses = allMUSes.computeAllMUSes();
        assertEquals(2, muses.size());
    }

    @Test
    public void testEclipseTestCase() throws ContradictionException,
            TimeoutException {
        this.solver.newVar(3);
        IVecInt clause = new VecInt();
        clause.push(-1);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(-2).push(3);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(-2).push(1);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(2);
        this.solver.addClause(clause);
        clause.clear();
        List<IVecInt> muses = allMUSes.computeAllMUSes();
        assertEquals(1, muses.size());
    }

    @Test
    public void testEclipseTestCase2() throws ContradictionException,
            TimeoutException {
        this.solver.newVar(4);
        IVecInt clause = new VecInt();
        clause.push(-1).push(2);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(-1).push(3);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(-2).push(-3);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(-4).push(1);
        this.solver.addClause(clause);
        clause.clear();
        List<IVecInt> muses = allMUSes.computeAllMUSes();
        assertEquals(0, muses.size());
    }

    @Test
    public void testExample1CADECedric() throws ContradictionException,
            TimeoutException {
        this.solver.newVar(5);
        IVecInt clause = new VecInt();

        clause.push(-4).push(5);
        this.solver.addClause(clause);
        clause.clear();

        clause.push(2).push(-3);
        this.solver.addClause(clause);
        clause.clear();

        clause.push(-4);
        this.solver.addClause(clause);
        clause.clear();

        clause.push(-1).push(2);
        this.solver.addClause(clause);
        clause.clear();

        clause.push(1);
        this.solver.addClause(clause);
        clause.clear();

        clause.push(1).push(-3).push(-5);
        this.solver.addClause(clause);
        clause.clear();

        clause.push(-1).push(3).push(4);
        this.solver.addClause(clause);
        clause.clear();

        clause.push(-2);
        this.solver.addClause(clause);
        clause.clear();

        List<IVecInt> muses = allMUSes.computeAllMUSes();
        assertEquals(2, muses.size());
    }

    @Test
    public void testExample3CADECedric() throws ContradictionException,
            TimeoutException {
        this.solver.newVar(6);
        IVecInt clause = new VecInt();

        clause.push(1);
        this.solver.addClause(clause);
        clause.clear();

        clause.push(2).push(4);
        this.solver.addClause(clause);
        clause.clear();

        clause.push(-2).push(-5);
        this.solver.addClause(clause);
        clause.clear();

        clause.push(1).push(4);
        this.solver.addClause(clause);
        clause.clear();

        clause.push(2).push(-3);
        this.solver.addClause(clause);
        clause.clear();

        clause.push(6);
        this.solver.addClause(clause);
        clause.clear();

        clause.push(3).push(-4);
        this.solver.addClause(clause);
        clause.clear();

        clause.push(-1);
        this.solver.addClause(clause);
        clause.clear();

        clause.push(-2).push(-3);
        this.solver.addClause(clause);
        clause.clear();

        clause.push(2).push(4).push(6);
        this.solver.addClause(clause);
        clause.clear();

        clause.push(5);
        this.solver.addClause(clause);
        clause.clear();

        clause.push(-6).push(4);
        this.solver.addClause(clause);
        clause.clear();

        clause.push(-5).push(-6);
        this.solver.addClause(clause);
        clause.clear();

        clause.push(1).push(-3).push(4);
        this.solver.addClause(clause);
        clause.clear();

        List<IVecInt> muses = allMUSes.computeAllMUSes();
        assertEquals(9, muses.size());
    }

    @Test
    public void testExample3IJCAICedric() throws ContradictionException,
            TimeoutException {
        this.solver.newVar(5);
        IVecInt clause = new VecInt();

        clause.push(4);
        this.solver.addClause(clause);
        clause.clear();

        clause.push(2).push(3);
        this.solver.addClause(clause);
        clause.clear();

        clause.push(1).push(2);
        this.solver.addClause(clause);
        clause.clear();

        clause.push(1).push(-3);
        this.solver.addClause(clause);
        clause.clear();

        clause.push(-2).push(-5);
        this.solver.addClause(clause);
        clause.clear();

        clause.push(-1).push(-2);
        this.solver.addClause(clause);
        clause.clear();

        clause.push(1).push(5);
        this.solver.addClause(clause);
        clause.clear();

        clause.push(-1).push(-5);
        this.solver.addClause(clause);
        clause.clear();

        clause.push(2).push(5);
        this.solver.addClause(clause);
        clause.clear();

        clause.push(-1).push(2).push(-3);
        this.solver.addClause(clause);
        clause.clear();

        clause.push(-1).push(2).push(-4);
        this.solver.addClause(clause);
        clause.clear();

        clause.push(1).push(-2).push(3);
        this.solver.addClause(clause);
        clause.clear();

        clause.push(1).push(-2).push(-4);
        this.solver.addClause(clause);
        clause.clear();

        List<IVecInt> muses = allMUSes.computeAllMUSes();

        assertEquals(17, muses.size());
    }

    public void testHardClauses() throws ContradictionException {
        FullClauseSelectorSolver<?> hardSolver = allMUSes.getSolverInstance();
        IVecInt hard = new VecInt();
        hard.push(1).push(2);
        hardSolver.addNonControlableClause(hard);
        IVecInt soft = new VecInt();
        soft.push(-1).push(3);
        hardSolver.addClause(soft);
        soft.clear();
        soft.push(-1).push(-3);
        hardSolver.addClause(soft);
        soft.clear();
        soft.push(-2);
        hardSolver.addClause(soft);
        soft.clear();
        List<IVecInt> muses = allMUSes.computeAllMUSes();
        assertEquals(1, muses.size());
        assertEquals(3, muses.get(0).size());
    }
}
