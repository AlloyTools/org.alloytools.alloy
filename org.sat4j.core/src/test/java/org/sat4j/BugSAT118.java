package org.sat4j;

import static org.junit.Assert.assertFalse;

import org.junit.Before;
import org.junit.Test;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;

public class BugSAT118 {

    private ISolver solver;

    @Before
    public void setUp() {
        solver = SolverFactory.newDefault();
    }

    @Test
    public void test() throws ContradictionException, TimeoutException {
        IVecInt clause = new VecInt();
        clause.push(-1).push(2);
        solver.addClause(clause);
        clause.clear();
        clause.push(1);
        solver.addClause(clause);
        clause.clear();
        clause.push(-2);
        solver.addClause(clause);
        assertFalse(solver.isSatisfiable());
        solver.unsatExplanation();
    }

}
