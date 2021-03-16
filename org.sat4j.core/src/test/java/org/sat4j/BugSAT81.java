package org.sat4j;

import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

import java.util.HashSet;
import java.util.Set;

import org.junit.Before;
import org.junit.Test;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.TimeoutException;
import org.sat4j.tools.GateTranslator;

public class BugSAT81 {

    private GateTranslator solver;

    /**
     * @throws java.lang.Exception
     */
    @Before
    public void setUp() throws Exception {
        solver = new GateTranslator(SolverFactory.newDefault());
    }

    @Test
    public void testSimplePhoneSATSmall() throws ContradictionException,
            TimeoutException {
        // SmallFeaturePhone (1)
        VecInt clause0 = new VecInt();
        clause0.push(1);
        solver.addClause(clause0);

        // Message (2)
        VecInt clause1 = new VecInt();
        clause1.push(1);
        clause1.push(-2);
        solver.addClause(clause1);

        VecInt clause2 = new VecInt();
        clause2.push(2);
        clause2.push(-1);
        solver.addClause(clause2);

        // SMS (3)
        VecInt clause3 = new VecInt();
        clause3.push(3);
        clause3.push(-2);
        solver.addClause(clause3);

        VecInt clause8 = new VecInt();
        clause8.push(2);
        clause8.push(-3);
        solver.addClause(clause8);

        // Extras (4)
        VecInt clause4 = new VecInt();
        clause4.push(-4);
        clause4.push(1);
        solver.addClause(clause4);

        // MP3 (5) v Camera (6)
        VecInt clause5 = new VecInt();
        clause5.push(-5);
        clause5.push(4);
        solver.addClause(clause5);

        VecInt clause6 = new VecInt();
        clause6.push(-6);
        clause6.push(4);
        solver.addClause(clause6);

        VecInt clause7 = new VecInt();
        clause7.push(5);
        clause7.push(6);
        clause7.push(-4);
        solver.addAtLeast(clause6, 1);

        assertTrue(solver.isSatisfiable());
        VecInt bound1 = new VecInt();
        bound1.push(3);
        assertNotNull(solver.findModel(bound1));

        VecInt bound2 = new VecInt();
        bound2.push(-3);
        assertNull(solver.findModel(bound2));

        VecInt bound3 = new VecInt();
        bound3.push(5);
        bound3.push(3);
        assertNotNull(solver.findModel(bound3));

        VecInt bound4 = new VecInt();
        bound4.push(5);
        bound4.push(-3);
        assertNull(solver.findModel(bound4));

        VecInt bound5 = new VecInt();
        bound5.push(4);
        bound5.push(-3);
        assertNull(solver.findModel(bound5)); // TODO Error

        VecInt bound6 = new VecInt();
        bound6.push(4);
        bound6.push(3);
        assertNotNull(solver.findModel(bound6));

        VecInt bound7 = new VecInt();
        bound7.push(4);

        int[] model = solver.findModel(bound7);
        assertNotNull(model);

        Set<Integer> satisfiedModel = new HashSet<Integer>();
        for (int i : model) {
            satisfiedModel.add(new Integer(i));
        }
        assertTrue(satisfiedModel.contains(new Integer(4)));
        assertTrue(satisfiedModel.contains(new Integer(1)));
        assertTrue(satisfiedModel.contains(new Integer(2)));
    }
}
