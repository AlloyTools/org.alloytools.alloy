package org.sat4j;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.junit.Test;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;

public class BugSAT164 {

    @Test
    public void testLearntUnit()
            throws ContradictionException, TimeoutException {
        ISolver solver = SolverFactory.newDefault();
        solver.newVar(5);
        solver.addClause(VecInt.of(-1, -2, 3));
        solver.addClause(VecInt.of(-1, 2, 3));
        solver.addClause(VecInt.of(1, -2, 3));
        solver.addClause(VecInt.of(1, 2, 3));
        solver.addClause(VecInt.of(-4, 5));
        solver.addClause(VecInt.of(4, 5));
        assertTrue(solver.isSatisfiable());
        int[] prime = solver.primeImplicant();
        assertEquals(2, prime.length);
        assertEquals(3, prime[0]);
        assertEquals(5, prime[1]);
    }

    @Test
    public void testInitialUnit()
            throws ContradictionException, TimeoutException {
        ISolver solver = SolverFactory.newDefault();
        solver.newVar(5);
        solver.addClause(VecInt.of(-1, -2, 3));
        solver.addClause(VecInt.of(-1, 2, 3));
        solver.addClause(VecInt.of(1, -2, 3));
        solver.addClause(VecInt.of(1, 2, 3));
        solver.addClause(VecInt.of(5));
        assertTrue(solver.isSatisfiable());
        int[] prime = solver.primeImplicant();
        assertEquals(2, prime.length);
        assertEquals(3, prime[0]);
        assertEquals(5, prime[1]);
    }
}
