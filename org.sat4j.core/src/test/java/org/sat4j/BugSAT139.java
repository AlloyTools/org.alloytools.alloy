package org.sat4j;

import static org.junit.Assert.assertEquals;

import org.junit.Test;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;
import org.sat4j.tools.ModelIterator;

public class BugSAT139 {

    @Test
    public void checkModelIterationWithExactly()
            throws ContradictionException, TimeoutException {
        ISolver solver = SolverFactory.newDefault();
        solver.newVar(5);
        solver.setExpectedNumberOfClauses(1);
        solver.addClause(new VecInt(new int[] { 1, 2, 3, 4, 5 }));
        solver.addExactly(new VecInt(new int[] { 1, 2, 3 }), 1);
        ModelIterator iterator = new ModelIterator(solver);
        while (iterator.isSatisfiable()) {
            iterator.model(); // to block that model
        }
        assertEquals(12, iterator.numberOfModelsFoundSoFar());
    }

    @Test
    public void checkModelIterationWithUnit()
            throws ContradictionException, TimeoutException {
        ISolver solver = SolverFactory.newDefault();
        solver.newVar(2);
        solver.setExpectedNumberOfClauses(3);
        solver.addClause(new VecInt(new int[] { 1 }));
        solver.addClause(new VecInt(new int[] { 1, 2 }));
        solver.addClause(new VecInt(new int[] { -1, -2 }));
        ModelIterator iterator = new ModelIterator(solver);
        while (iterator.isSatisfiable()) {
            iterator.model(); // to block that model
        }
        assertEquals(1, iterator.numberOfModelsFoundSoFar());
    }

    @Test(timeout = 1000)
    public void checkModelIterationWithUnitAndSatisfiableTrue()
            throws ContradictionException, TimeoutException {
        ISolver solver = SolverFactory.newDefault();
        solver.newVar(2);
        solver.setExpectedNumberOfClauses(3);
        solver.addClause(new VecInt(new int[] { 1 }));
        solver.addClause(new VecInt(new int[] { 1, 2 }));
        solver.addClause(new VecInt(new int[] { -1, -2 }));
        ModelIterator iterator = new ModelIterator(solver);
        while (iterator.isSatisfiable(true)) {
            iterator.model(); // to block that model
        }
        assertEquals(1, iterator.numberOfModelsFoundSoFar());
    }
}
