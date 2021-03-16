package org.sat4j;

import static org.junit.Assert.assertEquals;

import org.junit.Test;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;
import org.sat4j.tools.ModelIterator;
import org.sat4j.tools.SubModelIterator;

public class BugSAT109 {

    @Test
    public void testModelIterator() throws ContradictionException,
            TimeoutException {
        ModelIterator iterator = new ModelIterator(SolverFactory.newDefault());
        iterator.addClause(new VecInt(new int[] { 1, 2 }));
        iterator.addClause(new VecInt(new int[] { -1, -2 }));
        iterator.addClause(new VecInt(new int[] { -3, -4 }));
        iterator.addClause(new VecInt(new int[] { 5, 6 }));
        iterator.addClause(new VecInt(new int[] { -5, -6 }));
        iterator.addClause(new VecInt(new int[] { -1, 3 }));
        int counter = 0;
        int[] sub = new int[0];
        while (iterator.isSatisfiable()) {
            sub = iterator.model();
            counter++;
        }
        assertEquals(8, counter);
        assertEquals(6, sub.length);
    }

    @Test
    public void testSubModelIterator() throws ContradictionException,
            TimeoutException {
        IVecInt subset = new VecInt(new int[] { 1, 2, 3, 4 });
        ModelIterator iterator = new SubModelIterator(
                SolverFactory.newDefault(), subset);
        iterator.addClause(new VecInt(new int[] { 1, 2 }));
        iterator.addClause(new VecInt(new int[] { -1, -2 }));
        iterator.addClause(new VecInt(new int[] { -3, -4 }));
        iterator.addClause(new VecInt(new int[] { 5, 6 }));
        iterator.addClause(new VecInt(new int[] { -5, -6 }));
        iterator.addClause(new VecInt(new int[] { -1, 3 }));
        int counter = 0;
        int[] sub = new int[0];
        while (iterator.isSatisfiable()) {
            sub = iterator.model();
            counter++;
        }
        assertEquals(4, counter);
        assertEquals(4, sub.length);
    }
}
