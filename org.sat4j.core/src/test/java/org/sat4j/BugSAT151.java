package org.sat4j;

import static org.junit.Assert.assertTrue;

import org.junit.Test;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;

public class BugSAT151 {

    @Test
    public void testNonEmptyStats()
            throws ContradictionException, TimeoutException {
        IVecInt lits = new VecInt(new int[] { 1, 2, 3 });

        ISolver solver = SolverFactory.newDefault();
        solver.newVar(3);
        solver.addAtMost(lits, 2);

        assertTrue(solver.getStat().keySet().size() >= 17);
        solver.isSatisfiable();
        assertTrue(solver.getStat().keySet().size() >= 17);

    }

}
