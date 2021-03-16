package org.sat4j;

import static org.junit.Assert.assertEquals;

import org.junit.Before;
import org.junit.Test;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ISolver;
import org.sat4j.tools.DimacsOutputSolver;
import org.sat4j.tools.GateTranslator;
import org.sat4j.tools.ManyCore;
import org.sat4j.tools.ModelIterator;

public class TestSolverEngine {

    private ISolver solver;

    @Before
    public void startUp() {
        solver = SolverFactory.newDefault();
    }

    @Test
    public void testThatASolverReturnsItself() {
        assertEquals(solver, solver.getSolvingEngine());
    }

    @Test
    public void testThatItWorksWithOneDecorator() {
        GateTranslator gator = new GateTranslator(solver);
        assertEquals(solver, gator.getSolvingEngine());
    }

    @Test
    public void testThatItWorksWithTwoDecorators() {
        ModelIterator it = new ModelIterator(new GateTranslator(solver));
        assertEquals(solver, it.getSolvingEngine());
    }

    @Test(expected = UnsupportedOperationException.class)
    public void testThatItDoesNotWorkForManyCore() {
        ManyCore<ISolver> mc = new ManyCore<ISolver>(solver);
        mc.getSolvingEngine();
    }

    @Test(expected = UnsupportedOperationException.class)
    public void testThatItDoesNotWorkForOutputSolvers() {
        DimacsOutputSolver output = new DimacsOutputSolver();
        output.getSolvingEngine();
    }
}
