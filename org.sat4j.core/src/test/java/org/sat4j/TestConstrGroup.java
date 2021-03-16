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
package org.sat4j;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;
import org.sat4j.core.ConstrGroup;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;

public class TestConstrGroup {

    @Test
    public void testDeleteGroup() throws ContradictionException {
        ISolver solver = SolverFactory.newDefault();
        ConstrGroup g1 = new ConstrGroup();
        IVecInt clause = new VecInt(new int[] { 1, 2, -3 });
        solver.addClause(clause);
        // starting group
        clause.clear();
        clause.push(2).push(-3).push(-5);
        g1.add(solver.addClause(clause));
        clause.clear();
        clause.push(-3).push(-2).push(-4);
        g1.add(solver.addClause(clause));
        assertEquals(3, solver.nConstraints());
        g1.removeFrom(solver);
        assertEquals(1, solver.nConstraints());
    }

    @Test
    public void canPutAUnitClauseInAGroup() throws ContradictionException {
        ISolver solver = SolverFactory.newDefault();
        ConstrGroup g1 = new ConstrGroup();

        IVecInt clause = new VecInt(new int[] { 1 });
        g1.add(solver.addClause(clause));
        assertEquals(1, solver.nConstraints());
    }

    @Test
    public void checkBugReportedByThomas() throws ContradictionException {
        ISolver solver = SolverFactory.newDefault();
        ConstrGroup g1 = new ConstrGroup();

        IVecInt clause = new VecInt(new int[] { 1 });
        solver.addClause(clause);

        // starting group
        clause.clear();
        clause.push(2).push(-3).push(-5);
        g1.add(solver.addClause(clause));

        clause.clear();
        clause.push(-3).push(-2).push(-4);
        g1.add(solver.addClause(clause));
        assertEquals(3, solver.nConstraints());

        g1.removeFrom(solver);
        assertEquals(1, solver.nConstraints());
    }

    @Test
    public void checkItWorksAfterRunningTheSolver()
            throws ContradictionException, TimeoutException {
        ISolver solver = SolverFactory.newDefault();
        ConstrGroup g1 = new ConstrGroup();

        IVecInt clause = new VecInt(new int[] { 1 });
        solver.addClause(clause);

        // starting group
        clause.clear();
        clause.push(-1).push(-2).push(-3);
        g1.add(solver.addClause(clause));

        clause.clear();
        clause.push(-1).push(2).push(-3);
        g1.add(solver.addClause(clause));
        assertEquals(3, solver.nConstraints());
        assertTrue(solver.isSatisfiable());
        assertTrue(solver.model(1));
        assertFalse(solver.model(3));
        g1.removeFrom(solver);
        assertEquals(1, solver.nConstraints());
    }

    @Test
    public void checkGroupDoesWorkWhenClausesAreReducedByUnitPropgation()
            throws ContradictionException {
        ISolver solver = SolverFactory.newDefault();
        ConstrGroup g1 = new ConstrGroup();

        IVecInt clause = new VecInt(new int[] { 1 });
        solver.addClause(clause);

        // starting group
        clause.clear();
        clause.push(-1).push(-2);
        g1.add(solver.addClause(clause));
        assertEquals(1, g1.size());
    }

    @Test
    public void checkTheExpectedWayToDealWithUnitClausesToRemove()
            throws ContradictionException, TimeoutException {
        ISolver solver = SolverFactory.newDefault();
        ConstrGroup g1 = new ConstrGroup();

        IVecInt clause = new VecInt(new int[] { 1 });
        solver.addClause(clause);

        // starting group
        clause.clear();
        clause.push(2).push(-3);
        g1.add(solver.addClause(clause));

        clause.clear();
        clause.push(-2).push(4);
        g1.add(solver.addClause(clause));

        IVecInt unitClauses = new VecInt(new int[] { 3, -4 });

        assertFalse(solver.isSatisfiable(unitClauses));

        g1.removeFrom(solver);
        assertTrue(solver.isSatisfiable(unitClauses));
    }
}
