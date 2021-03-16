package org.sat4j;

import static org.junit.Assert.assertEquals;

import org.junit.Test;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IConstr;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;

public class BugSAT155 {

    @Test
    public void testBasicDump() throws ContradictionException {
        ISolver solver = SolverFactory.newDefault();
        IVecInt literals = new VecInt(new int[] { 1, 2, 3 });
        IConstr c1 = solver.addClause(literals);
        assertEquals("1 2 3 0", c1.dump());

    }

    @Test
    public void testBasicDumpNegativeLiteral() throws ContradictionException {
        ISolver solver = SolverFactory.newDefault();
        IVecInt literals = new VecInt(new int[] { 1, -2, 3 });
        IConstr c1 = solver.addClause(literals);
        assertEquals("1 -2 3 0", c1.dump());

    }

    @Test
    public void testBasicDump4Card() throws ContradictionException {
        ISolver solver = SolverFactory.newDefault();
        IVecInt literals = new VecInt(new int[] { 1, 2, 3 });
        IConstr c1 = solver.addAtLeast(literals, 2);
        assertEquals("x1 + x2 + x3 >= 2", c1.dump());

    }

    @Test
    public void testBasicDump4CardNegativeLiteral()
            throws ContradictionException {
        ISolver solver = SolverFactory.newDefault();
        IVecInt literals = new VecInt(new int[] { 1, -2, 3 });
        IConstr c1 = solver.addAtLeast(literals, 2);
        assertEquals("x1 + ~x2 + x3 >= 2", c1.dump());

    }

}
