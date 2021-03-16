package org.sat4j;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;

import org.junit.Test;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;

public class BugSAT162 {

    @Test
    public void testSatisfiable()
            throws TimeoutException, ContradictionException {
        ISolver solver = SolverFactory.newDefault();
        solver.newVar(4);
        IVecInt clause = new VecInt(new int[] { 1, 2, 3, 4 });
        solver.addClause(clause);
        assertTrue(solver.isSatisfiable());
        IVecInt model = new VecInt(solver.model());
        int[] decisions = solver.decisions();
        for (int d : decisions) {
            assertTrue(model.contains(d));
        }
    }

    @Test(expected = IllegalStateException.class)
    public void testUnsatisfiable()
            throws TimeoutException, ContradictionException {
        ISolver solver = SolverFactory.newDefault();
        solver.newVar(2);
        IVecInt clause = new VecInt(new int[] { 1, 2 });
        solver.addClause(clause);
        clause.clear();
        clause.push(-1);
        solver.addClause(clause);
        clause.clear();
        clause.push(-2);
        solver.addClause(clause);
        assertFalse(solver.isSatisfiable());
        solver.decisions();
    }

    @Test
    public void testSatisfiableWithoutCallingModel()
            throws TimeoutException, ContradictionException {
        ISolver solver = SolverFactory.newDefault();
        solver.newVar(4);
        IVecInt clause = new VecInt(new int[] { 1, 2, 3, 4 });
        solver.addClause(clause);
        assertTrue(solver.isSatisfiable());
        int[] decisions = solver.decisions();
        for (int d : decisions) {
            assertNotEquals(0, d);
        }
    }
}
