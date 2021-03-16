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

import static org.junit.Assert.assertTrue;

import org.junit.Test;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.minisat.core.DataStructureFactory;
import org.sat4j.minisat.core.IOrder;
import org.sat4j.minisat.core.Solver;
import org.sat4j.minisat.orders.SubsetVarOrder;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;
import org.sat4j.tools.TextOutputTracing;

public class BugSAT50 {

    @Test
    public void test() throws ContradictionException, TimeoutException {
        Solver<DataStructureFactory> solver = SolverFactory.newGlucose();
        int[] backdoor = { 1, 2, 3 };
        IOrder order = new SubsetVarOrder(backdoor);
        solver.setOrder(order);
        IVecInt clause = new VecInt();
        clause.push(1).push(4);
        solver.addClause(clause);
        clause = new VecInt();
        clause.push(2).push(5);
        solver.addClause(clause);
        clause = new VecInt();
        clause.push(3).push(6);
        solver.addClause(clause);
        assertTrue(solver.isSatisfiable());
    }

    @Test
    public void test2() throws ContradictionException, TimeoutException {
        Solver<DataStructureFactory> solver = SolverFactory.newGlucose();
        int[] backdoor = { 1, 2, 3 };
        IOrder order = new SubsetVarOrder(backdoor);
        solver.setOrder(order);
        IVecInt clause = new VecInt();
        clause.push(-1).push(4);
        solver.addClause(clause);
        clause = new VecInt();
        clause.push(-2).push(5);
        solver.addClause(clause);
        clause = new VecInt();
        clause.push(-3).push(6);
        solver.addClause(clause);
        assertTrue(solver.isSatisfiable());
    }

    @Test(expected = TimeoutException.class)
    public void test3() throws ContradictionException, TimeoutException {
        Solver<DataStructureFactory> solver = SolverFactory.newGlucose();
        solver.setSearchListener(new TextOutputTracing<Object>(null));
        int[] backdoor = { 1, 2, 3 };
        IOrder order = new SubsetVarOrder(backdoor);
        solver.setOrder(order);
        IVecInt clause = new VecInt();
        clause.push(-1).push(4).push(7);
        solver.addClause(clause);
        clause = new VecInt();
        clause.push(-2).push(5).push(7);
        solver.addClause(clause);
        clause = new VecInt();
        clause.push(-3).push(6).push(5);
        solver.addClause(clause);
        clause = new VecInt();
        clause.push(1).push(2).push(3).push(7).push(8);
        solver.addClause(clause);
        solver.isSatisfiable();
    }

    @Test
    public void testJeanGuy1() throws ContradictionException, TimeoutException {
        Solver<DataStructureFactory> solver = SolverFactory.newGlucose();
        int[] backdoor = { 1, 2, 3, 4 };
        IOrder order = new SubsetVarOrder(backdoor);
        solver.setOrder(order);
        IVecInt clause = new VecInt();
        clause.push(-1).push(5);
        solver.addClause(clause);
        clause = new VecInt();
        clause.push(-2).push(3).push(5);
        solver.addClause(clause);
        clause = new VecInt();
        clause.push(-4).push(5);
        solver.addClause(clause);
        assertTrue(solver.isSatisfiable());
    }

    @Test
    public void testJeanGuy2() throws ContradictionException, TimeoutException {
        Solver<DataStructureFactory> solver = SolverFactory.newGlucose();
        int[] backdoor = { 5 };
        IOrder order = new SubsetVarOrder(backdoor);
        solver.setOrder(order);
        IVecInt clause = new VecInt();
        clause.push(-1).push(5);
        solver.addClause(clause);
        clause = new VecInt();
        clause.push(-2).push(3).push(5);
        solver.addClause(clause);
        clause = new VecInt();
        clause.push(-4).push(5);
        solver.addClause(clause);
        assertTrue(solver.isSatisfiable());
    }
}
