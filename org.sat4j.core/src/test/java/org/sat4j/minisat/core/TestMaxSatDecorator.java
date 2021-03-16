package org.sat4j.minisat.core;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.junit.Before;
import org.junit.Test;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.opt.MaxSatDecorator;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;
import org.sat4j.tools.OptToSatAdapter;

/**
 * Maxsat test case to cover the situation of a Maxsat solver which requires
 * several iterations before finding the optimal solution. The aim of this test
 * is to cover a nominal case in a try in the MaxSat decorator.
 * 
 * @author leberre
 * 
 */
public class TestMaxSatDecorator {

    private MaxSatDecorator maxsat;
    private OptToSatAdapter optimizer;

    @Before
    public void setUp() {
        maxsat = new MaxSatDecorator(SolverFactory.newDefault());
        optimizer = new OptToSatAdapter(maxsat);
    }

    @Test
    public void test() throws ContradictionException, TimeoutException {
        optimizer.newVar(4);
        IVecInt clause = new VecInt();
        clause.push(1).push(2);
        optimizer.addClause(clause);
        clause.clear();
        clause.push(-1).push(2);
        optimizer.addClause(clause);
        clause.clear();
        clause.push(1).push(-2);
        optimizer.addClause(clause);
        clause.clear();
        clause.push(-1).push(-2);
        optimizer.addClause(clause);
        clause.clear();
        clause.push(3).push(4);
        optimizer.addClause(clause);
        clause.clear();
        clause.push(-3).push(4);
        optimizer.addClause(clause);
        clause.clear();
        clause.push(3).push(-4);
        optimizer.addClause(clause);
        clause.clear();
        clause.push(-3).push(-4);
        optimizer.addClause(clause);
        clause.clear();
        clause.push(1).push(2).push(3).push(4);
        optimizer.addClause(clause);
        clause.clear();
        assertTrue(optimizer.isSatisfiable());
        assertTrue(optimizer.isOptimal());
        assertEquals(2, maxsat.getObjectiveValue());
    }

}
