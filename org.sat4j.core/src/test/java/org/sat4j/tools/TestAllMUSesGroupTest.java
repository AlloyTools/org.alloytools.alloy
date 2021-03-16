package org.sat4j.tools;

import static org.junit.Assert.assertEquals;

import java.util.List;

import org.junit.Before;
import org.junit.Test;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IGroupSolver;
import org.sat4j.specs.IVecInt;

public class TestAllMUSesGroupTest {
    private IGroupSolver solver;
    private AllMUSes allMUSes;

    @Before
    public void setUp() throws Exception {
        this.allMUSes = new AllMUSes(true, SolverFactory.instance());
        this.solver = allMUSes.getSolverInstance();
    }

    @Test
    public void testSimpleCase() {
        IVecInt c1 = new VecInt();
        IVecInt c2 = new VecInt();
        IVecInt c3 = new VecInt();
        IVecInt c4 = new VecInt();
        IVecInt c5 = new VecInt();

        c1.push(1);
        c2.push(2);
        c3.push(-1).push(-2);
        c4.push(3);
        c5.push(-3);

        this.solver.newVar(3);
        System.out.println("mus should be = [1,2,3 / 4,5]");

        try {
            this.solver.addClause(c1, 1);
            this.solver.addClause(c2, 2);
            this.solver.addClause(c3, 3);
            this.solver.addClause(c4, 4);
            this.solver.addClause(c5, 5);

            List<IVecInt> muses = allMUSes.computeAllMUSes();

            assertEquals(muses.size(), 2);

        } catch (ContradictionException e) {
            e.printStackTrace();
        }

    }

    @Test
    public void testSimpleCaseWithGroups() {
        IVecInt c1 = new VecInt();
        IVecInt c2 = new VecInt();
        IVecInt c3 = new VecInt();
        IVecInt c4 = new VecInt();
        IVecInt c5 = new VecInt();

        c1.push(1);
        c2.push(2);
        c3.push(-1).push(-2);
        c4.push(3);
        c5.push(-3);

        this.solver.newVar(3);

        System.out.println("mus should be = [1 / 2]");

        try {
            this.solver.addClause(c1, 1);
            this.solver.addClause(c2, 1);
            this.solver.addClause(c3, 1);
            this.solver.addClause(c4, 2);
            this.solver.addClause(c5, 2);

            List<IVecInt> muses = allMUSes.computeAllMUSes();

            assertEquals(muses.size(), 2);

        } catch (ContradictionException e) {
            e.printStackTrace();
        }
    }

    @Test
    public void testSimpleCaseWithGroups2() {
        IVecInt c1 = new VecInt();
        IVecInt c2 = new VecInt();
        IVecInt c3 = new VecInt();
        IVecInt c4 = new VecInt();
        IVecInt c5 = new VecInt();

        c1.push(1);
        c2.push(2);
        c3.push(-1).push(-2);
        c4.push(3);
        c5.push(-3);

        this.solver.newVar(3);

        System.out.println("mus should be = [1,2]");

        try {
            this.solver.addClause(c1, 1);
            this.solver.addClause(c2, 2);
            this.solver.addClause(c3, 1);
            this.solver.addClause(c4, 2);
            this.solver.addClause(c5, 1);

            List<IVecInt> muses = allMUSes.computeAllMUSes();

            assertEquals(muses.size(), 1);

        } catch (ContradictionException e) {
            e.printStackTrace();
        }
    }

    @Test
    public void testSimpleCaseWithGroups3() {
        IVecInt c1 = new VecInt();
        IVecInt c2 = new VecInt();
        IVecInt c3 = new VecInt();
        IVecInt c4 = new VecInt();
        IVecInt c5 = new VecInt();

        c1.push(1);
        c2.push(2);
        c3.push(-1).push(-2);
        c4.push(3);
        c5.push(-3);

        this.solver.newVar(3);

        System.out.println("mus should be = [1,2]");

        try {
            this.solver.addClause(c1, 1);
            this.solver.addClause(c2, 2);
            this.solver.addClause(c3, 3);
            this.solver.addClause(c4, 2);
            this.solver.addClause(c5, 1);

            List<IVecInt> muses = allMUSes.computeAllMUSes();

            assertEquals(muses.size(), 1);

        } catch (ContradictionException e) {
            e.printStackTrace();
        }
    }

    @Test
    public void testSimpleCaseWithGroups4() {
        IVecInt c1 = new VecInt();
        IVecInt c2 = new VecInt();
        IVecInt c3 = new VecInt();
        IVecInt c4 = new VecInt();
        IVecInt c5 = new VecInt();

        c1.push(1);
        c2.push(2);
        c3.push(-1).push(-2);
        c4.push(3);
        c5.push(-3);

        this.solver.newVar(3);

        System.out.println("mus should be = [1,4 / 1,2,3]");

        try {
            this.solver.addClause(c1, 1);
            this.solver.addClause(c2, 2);
            this.solver.addClause(c3, 3);
            this.solver.addClause(c4, 4);
            this.solver.addClause(c5, 1);

            List<IVecInt> muses = allMUSes.computeAllMUSes();

            assertEquals(muses.size(), 2);

        } catch (ContradictionException e) {
            e.printStackTrace();
        }
    }

    @Test
    public void testVerySimpleCase() {
        IVecInt c1 = new VecInt();
        IVecInt c2 = new VecInt();

        c1.push(1);
        c2.push(-1);

        this.solver.newVar(1);
        System.out.println("mus should be = [1,2]");

        try {
            this.solver.addClause(c1, 1);
            this.solver.addClause(c2, 2);

            List<IVecInt> muses = allMUSes.computeAllMUSes();

            assertEquals(muses.size(), 1);

        } catch (ContradictionException e) {
            e.printStackTrace();
        }
    }
}
