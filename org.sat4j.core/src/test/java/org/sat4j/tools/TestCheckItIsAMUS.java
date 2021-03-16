package org.sat4j.tools;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Before;
import org.junit.Test;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.IVecInt;

public class TestCheckItIsAMUS {

    private CheckMUSSolutionListener check;

    @Before
    public void setUp() throws Exception {
        check = new CheckMUSSolutionListener(SolverFactory.instance());
    }

    @Test
    public void testItWorksOnSimpleMUSes() {
        IVecInt c1 = new VecInt();

        c1.push(1);
        check.addOriginalClause(c1);

        c1.clear();
        c1.push(2);
        check.addOriginalClause(c1);

        c1.clear();
        c1.push(-1).push(-2);
        check.addOriginalClause(c1);

        IVecInt mus = new VecInt();
        mus.push(1).push(2).push(3);

        assertTrue(check.checkThatItIsAMUS(mus));
    }

    @Test
    public void testItWorksOnSimpleNonMUSes() {
        IVecInt c1 = new VecInt();

        c1.push(1);
        check.addOriginalClause(c1);

        c1.clear();
        c1.push(2);
        check.addOriginalClause(c1);

        // c1.clear();
        // c1.push(-1).push(-2);
        // check.addOriginalClause(c1);

        IVecInt mus = new VecInt();
        mus.push(1).push(2);

        assertFalse(check.checkThatItIsAMUS(mus));
    }

}
