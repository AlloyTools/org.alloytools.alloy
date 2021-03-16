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
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;

/**
 * 
 * @author daniel
 * @since 2.2
 */
public class BugReset {

    @Test
    public void testBugKostya() throws TimeoutException, ContradictionException {
        ISolver solver = SolverFactory.newDefault();
        solver.setTimeout(3600);

        boolean res;

        // test empty
        assertTrue(solver.isSatisfiable());
        solver.reset();

        // test one statement
        solver.newVar(1);
        int[] clause = new int[] { -4 };
        // the addClause method in this case returns null! It is imposible to
        // remove this
        // fact from a knowledge base. Javadoc does not say anything about this
        // exception.
        solver.addClause(new VecInt(clause));
        res = solver.isSatisfiable();
        assertTrue(res);
        solver.reset();

        // test multiply statements
        solver.newVar(4);
        clause = new int[] { -1, -2, -3, 4 };
        solver.addClause(new VecInt(clause));
        clause = new int[] { 1 };
        solver.addClause(new VecInt(clause));
        clause = new int[] { 2 };
        solver.addClause(new VecInt(clause));
        clause = new int[] { 3 };
        solver.addClause(new VecInt(clause));
        assertTrue(solver.isSatisfiable()); // ArrayIndexOutOfBoundsException
    }

    @Test
    public void testWithReset() throws TimeoutException, ContradictionException {
        ISolver solver = SolverFactory.newDefault();
        int[] clause;
        boolean res;

        // prepare the solver to accept MAXVAR variables. MANDATORY
        solver.newVar(4);
        // not mandatory for SAT solving. MANDATORY for MAXSAT solving
        solver.setExpectedNumberOfClauses(6);
        // Feed the solver using Dimacs format, using arrays of int
        // (best option to avoid dependencies on SAT4J IVecInt)

        // test empty
        res = solver.isSatisfiable();
        assertTrue(res);
        solver.reset();

        // test one clause
        solver.newVar(1);
        clause = new int[] { -4 };
        solver.addClause(new VecInt(clause));
        res = solver.isSatisfiable();
        assertTrue(res);
        solver.reset();

        // test multiply statements
        solver.newVar(4);
        addData(solver);
        assertTrue(solver.isSatisfiable());

        clause = new int[] { -4 };
        solver.addClause(new VecInt(clause));
        try {
            addData(solver);
            res = solver.isSatisfiable();
        } catch (ContradictionException e) {
            res = false;
        }
        assertFalse(res);
        solver.reset();
    }

    private void addData(ISolver solver) throws ContradictionException {
        int[] clause = new int[] { -1, -2, -3, 4 };
        solver.addClause(new VecInt(clause));

        clause = new int[] { 1 };
        solver.addClause(new VecInt(clause));

        clause = new int[] { 2 };
        solver.addClause(new VecInt(clause));

        clause = new int[] { 3 };
        solver.addClause(new VecInt(clause));

    }

    @Test
    public void problemTest() throws TimeoutException, ContradictionException {
        ISolver solver = SolverFactory.newDefault();
        solver.setTimeout(3600);
        solver.newVar(4);
        solver.setExpectedNumberOfClauses(5);

        for (int i = 0; i < 10; i++) {
            solve(solver, new int[] {}, true);
            solve(solver, new int[] { -4 }, false);
        }
    }

    private void solve(ISolver solver, int[] clause, boolean value)
            throws ContradictionException, TimeoutException {
        boolean res = true;
        try {
            if (clause.length > 0) {
                solver.addClause(new VecInt(clause));
            }
            clause = new int[] { -1, 2, 4 };
            solver.addClause(new VecInt(clause));
            clause = new int[] { 1, -2 };
            solver.addClause(new VecInt(clause));
            clause = new int[] { 1, 2 };
            solver.addClause(new VecInt(clause));
            clause = new int[] { -1, -2 };
            solver.addClause(new VecInt(clause));

        } catch (ContradictionException e) {
            res = false;
        }
        if (res) {
            res = solver.isSatisfiable();
        }
        solver.reset();
        assertEquals(res, value);
    }

    @Test
    public void problemTest2() throws TimeoutException, ContradictionException {
        boolean create = false;

        ISolver solver = null;
        if (!create) {
            solver = getSolver(solver, 4, 5);
        }

        for (int i = 0; i < 10; i++) {
            solve2(getSolver(solver, 4, 5), new int[] { -4 }, false);
            solve2(getSolver(solver, 4, 5), new int[] {}, true);
        }
    }

    private void solve2(ISolver solver, int[] clause, boolean value)
            throws ContradictionException, TimeoutException {
        boolean res = true;

        try {

            int[] lclause = new int[] { -1, -2, -3, 4 };
            solver.addClause(new VecInt(lclause));
            lclause = new int[] { 1 };
            solver.addClause(new VecInt(lclause));
            lclause = new int[] { 2 };
            solver.addClause(new VecInt(lclause));
            lclause = new int[] { 3 };
            solver.addClause(new VecInt(lclause));
            if (clause.length > 0) {
                solver.addClause(new VecInt(clause));
            }

        } catch (ContradictionException e) {
            res = false;
        }
        if (res) {
            res = solver.isSatisfiable();
        }
        assertEquals(res, value);
    }

    private ISolver getSolver(ISolver solver, int vars, int clauses) {
        if (solver == null) {
            solver = SolverFactory.newDefault();
            solver.setTimeout(3600);
            solver.newVar(vars);
            solver.setExpectedNumberOfClauses(clauses);
        } else {
            solver.reset();
            solver.clearLearntClauses();
        }
        return solver;
    }
}
