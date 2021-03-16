package org.sat4j;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Before;
import org.junit.Test;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.opt.MinOneDecorator;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;
import org.sat4j.tools.OptToSatAdapter;

public class BugSAT107 {

    private OptToSatAdapter solver;

    @Before
    public void setUp() throws ContradictionException {
        solver = new OptToSatAdapter(new MinOneDecorator(
                SolverFactory.newDefault()));
        solver.newVar(100);
        IVecInt clause = new VecInt();
        for (int i = 2; i < 100; i++) {
            clause.push(-1).push(i);
            solver.addClause(clause);
            clause.clear();
            clause.push(-i).push(i + 1);
            solver.addClause(clause);
        }
        clause.clear();
        for (int i = 1; i <= 10; i++) {
            clause.push(i);
        }
        solver.addClause(clause);

    }

    @Test
    public void testOptimalSolutionfound() throws ContradictionException,
            TimeoutException {
        solver.setTimeoutOnConflicts(100);
        assertTrue(solver.isSatisfiable());
        assertTrue(solver.isOptimal());
    }

    @Test
    public void testNonOptimalSolutionfound() throws ContradictionException,
            TimeoutException {
        solver.setTimeoutOnConflicts(3);
        assertTrue(solver.isSatisfiable());
        assertFalse(solver.isOptimal());
    }

    @Test(expected = TimeoutException.class)
    public void testNoSolutionfound() throws TimeoutException {
        solver.setTimeoutOnConflicts(1);
        solver.isSatisfiable();
    }

    @Test
    public void testNoSolutionExists() throws ContradictionException,
            TimeoutException {
        IVecInt clause = new VecInt();
        clause.push(100).push(99);
        solver.addClause(clause);
        clause.clear();
        clause.push(-99);
        solver.addClause(clause);
        clause.clear();
        clause.push(-100);
        solver.addClause(clause);
        clause.clear();
        assertFalse(solver.isSatisfiable());
    }
}
