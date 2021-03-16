package org.sat4j.tools;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.junit.Before;
import org.junit.Test;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;

public class NegationDecoratorTest {

    private ISolver solver;

    @Before
    public void setUp() throws Exception {
        solver = new NegationDecorator<ISolver>(SolverFactory.newDefault());
    }

    @Test
    public void testNegatingASingleClause() throws TimeoutException,
            ContradictionException {
        solver.newVar(3);
        IVecInt clause = new VecInt();
        clause.push(1).push(2).push(3);
        solver.addClause(clause);
        assertTrue(solver.isSatisfiable());
        int[] model = solver.model();
        assertEquals(-1, model[0]);
        assertEquals(-2, model[1]);
        assertEquals(-3, model[2]);
    }

    @Test
    public void testNegatingTwoClauses() throws TimeoutException,
            ContradictionException {
        solver.newVar(3);
        IVecInt clause = new VecInt();
        clause.push(1).push(2).push(3);
        solver.addClause(clause);
        clause.clear();
        clause.push(-1).push(2).push(3);
        solver.addClause(clause);
        assertTrue(solver.isSatisfiable());
        int[] model = solver.model();
        assertEquals(-2, model[1]);
        assertEquals(-3, model[2]);
    }

}
