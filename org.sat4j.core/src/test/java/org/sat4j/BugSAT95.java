package org.sat4j;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.junit.Before;
import org.junit.Test;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.opt.MinOneDecorator;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;
import org.sat4j.tools.FullClauseSelectorSolver;
import org.sat4j.tools.OptToSatAdapter;

public class BugSAT95 {

    private ISolver solver;
    private MinOneDecorator minOne;
    private OptToSatAdapter adapter;

    @Before
    public void setUp() throws ContradictionException {
        solver = SolverFactory.newDefault();
        minOne = new MinOneDecorator(solver);
        adapter = new OptToSatAdapter(minOne);
        IVecInt clause = new VecInt();
        clause.push(1).push(2);
        minOne.addClause(clause);
        clause.clear();
        clause = new VecInt();
        clause.push(1).push(-3);
        minOne.addClause(clause);
        clause.clear();
        clause = new VecInt();
        clause.push(1).push(3).push(4);
        minOne.addClause(clause);
        clause.clear();
    }

    @Test
    public void testOptimalSolutionWithMinOneIsSatisfiablePlusModel()
            throws ContradictionException, TimeoutException {

        assertTrue(adapter.isSatisfiable());
        int[] model = adapter.model();
        assertEquals(4, model.length);
        assertEquals(1, model[0]);
        assertEquals(-2, model[1]);
        assertEquals(-3, model[2]);
        assertEquals(-4, model[3]);
    }

    @Test
    public void testOptimalSolutionWithMinOneFindModel()
            throws ContradictionException, TimeoutException {
        int[] model = adapter.findModel();
        assertEquals(4, model.length);
        assertEquals(1, model[0]);
        assertEquals(-2, model[1]);
        assertEquals(-3, model[2]);
        assertEquals(-4, model[3]);
    }

    @Test
    public void testOptimalSolutionWithFullClauseSelectorIsSatisfiablePlusModel()
            throws ContradictionException, TimeoutException {

        FullClauseSelectorSolver<ISolver> softSolver = new FullClauseSelectorSolver<ISolver>(
                adapter, false);
        assertTrue(softSolver.isSatisfiable());
        int[] model = softSolver.model();
        assertEquals(4, model.length);
        assertEquals(1, model[0]);
        assertEquals(-2, model[1]);
        assertEquals(-3, model[2]);
        assertEquals(-4, model[3]);
    }

    @Test
    public void testOptimalSolutionWithFullClauseSelectorFindModel()
            throws ContradictionException, TimeoutException {

        FullClauseSelectorSolver<ISolver> softSolver = new FullClauseSelectorSolver<ISolver>(
                adapter, false);
        int[] model = softSolver.findModel();
        assertEquals(4, model.length);
        assertEquals(1, model[0]);
        assertEquals(-2, model[1]);
        assertEquals(-3, model[2]);
        assertEquals(-4, model[3]);
    }
}
