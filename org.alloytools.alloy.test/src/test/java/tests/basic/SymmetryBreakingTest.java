package tests.basic;

import java.util.ArrayList;
import java.util.List;

import junit.framework.TestCase;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.Statistics;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

/**
 * Tests symmetry breaking code for total orderings and acyclic relations.
 *
 * @author Emina Torlak
 */
public class SymmetryBreakingTest extends TestCase {

    private static final int   USIZE = 10;
    private final TupleFactory factory;
    private final Relation     to1, ord1, first1, last1, to2, ord2, first2, last2, to3, ord3, first3, last3, ac1, ac2,
                    ac3, r1, r2;
    private Bounds             bounds;
    private int                pVars, iVars, clauses;
    private final Solver       solver;

    public SymmetryBreakingTest(String arg0) {
        super(arg0);
        this.solver = new Solver();

        List<String> atoms = new ArrayList<String>(USIZE);
        for (int i = 0; i < USIZE; i++) {
            atoms.add("" + i);
        }
        final Universe universe = new Universe(atoms);
        this.factory = universe.factory();

        to1 = Relation.binary("to1");
        ord1 = Relation.unary("ord1");
        first1 = Relation.unary("first1");
        last1 = Relation.unary("last1");

        to2 = Relation.binary("to2");
        ord2 = Relation.unary("ord2");
        first2 = Relation.unary("first2");
        last2 = Relation.unary("last2");

        to3 = Relation.binary("to3");
        ord3 = Relation.unary("ord3");
        first3 = Relation.unary("first3");
        last3 = Relation.unary("last3");

        ac1 = Relation.binary("ac1");
        ac2 = Relation.binary("ac2");
        ac3 = Relation.binary("ac3");

        r1 = Relation.unary("r1");
        r2 = Relation.binary("r2");
    }

    @Override
    protected void setUp() throws Exception {
        super.setUp();
        bounds = new Bounds(factory.universe());
    }

    private Instance solve(Formula f, Bounds b) {

        final Solution sol = solver.solve(f, b);
        final Statistics stats = sol.stats();
        pVars = stats.primaryVariables();
        iVars = stats.variables() - pVars;
        clauses = stats.clauses();
        return sol.instance();

    }

    private Instance solve(Formula f) {
        return solve(f, bounds);
    }

    private void assertPrimVarNum(int primVars) {
        assertEquals(primVars, pVars);
    }

    private void assertAuxVarNum(int auxVars) {
        assertEquals(auxVars, iVars);
    }

    private void assertClauseNum(int clauses) {
        assertEquals(clauses, this.clauses);
    }

    public void testTotalOrdering() {
        bounds.bound(to1, factory.area(factory.tuple("0", "0"), factory.tuple("4", "4")));
        bounds.bound(ord1, factory.setOf("0", "1", "2", "3", "4"));
        bounds.bound(first1, bounds.upperBound(ord1));
        bounds.bound(last1, bounds.upperBound(ord1));
        final Formula ordered1 = to1.totalOrder(ord1, first1, last1);
        assertNotNull(solve(to1.some().and(ordered1)));
        assertPrimVarNum(0);
        assertAuxVarNum(0);
        assertClauseNum(0);

        bounds.bound(r1, factory.range(factory.tuple("0"), factory.tuple("4")));
        assertNotNull(solve(to1.join(r1).some().and(ordered1)));
        assertPrimVarNum(bounds.upperBound(r1).size());

        bounds.boundExactly(r1, bounds.upperBound(r1));
        assertNotNull(solve(to1.join(r1).some().and(ordered1)));
        assertPrimVarNum(0);

        bounds.bound(to2, factory.setOf("5", "6", "7", "8", "9").product(factory.setOf("5", "7", "8")));
        bounds.bound(ord2, factory.setOf("5", "7", "8"));
        bounds.bound(first2, bounds.upperBound(ord2));
        bounds.bound(last2, bounds.upperBound(ord2));
        final Formula ordered2 = to2.totalOrder(ord2, first2, last2);
        assertNotNull(solve(to1.difference(to2).some().and(ordered2).and(ordered1)));
        assertPrimVarNum(0);
        assertAuxVarNum(0);
        assertClauseNum(0);

        bounds.bound(to3, factory.allOf(2));
        bounds.bound(ord3, factory.allOf(1));
        bounds.bound(first3, factory.setOf("9"));
        bounds.bound(last3, factory.setOf("8"));
        final Formula ordered3 = to3.totalOrder(ord3, first3, last3);
        assertNotNull(solve(to3.product(to1).some().and(ordered1).and(ordered3)));
        assertPrimVarNum(bounds.upperBound(to3).size() + bounds.upperBound(ord3).size() + 2);

        // SAT solver takes a while
        // bounds.boundExactly(r2, factory.setOf(factory.tuple("9","8")));
        // assertNotNull(solve(r2.in(to3).and(ordered3)));
        bounds.bound(to3, factory.allOf(2));
        bounds.bound(ord3, factory.setOf("3"));
        bounds.bound(first3, factory.allOf(1));
        bounds.bound(last3, factory.allOf(1));

        Instance instance = solve(ordered3);
        assertNotNull(instance);
        assertTrue(instance.tuples(to3).isEmpty());
        assertTrue(instance.tuples(ord3).equals(bounds.upperBound(ord3)));
        assertTrue(instance.tuples(first3).equals(bounds.upperBound(ord3)));
        assertTrue(instance.tuples(last3).equals(bounds.upperBound(ord3)));
    }

    public void testAcyclic() {
        bounds.bound(ac1, factory.area(factory.tuple("0", "0"), factory.tuple("4", "4")));
        assertNotNull(solve(ac1.some().and(ac1.acyclic())));
        assertPrimVarNum(10);

        bounds.bound(r1, factory.range(factory.tuple("0"), factory.tuple("4")));
        assertNotNull(solve(ac1.join(r1).some().and(ac1.acyclic())));
        assertPrimVarNum(10 + bounds.upperBound(r1).size());

        TupleSet ac2b = factory.setOf("5", "6", "7", "8");
        ac2b = ac2b.product(ac2b);
        bounds.bound(ac2, ac2b);
        assertNotNull(solve(ac1.difference(ac2).some().and(ac1.acyclic()).and(ac2.acyclic())));
        assertPrimVarNum(10 + 6);

        bounds.boundExactly(r2, factory.setOf(factory.tuple("5", "6")));
        assertNotNull(solve(ac2.join(r2).some().and(ac2.acyclic())));

        final TupleSet ac3Bound = factory.allOf(2);
        ac3Bound.remove(factory.tuple("9", "9"));
        bounds.bound(ac3, ac3Bound);

        assertNotNull(solve(ac1.difference(ac2).union(ac3).some().and(ac1.acyclic()).and(ac2.acyclic())));
        assertPrimVarNum(ac3Bound.size() + 10 + 6);

        bounds.bound(to3, factory.allOf(2));
        bounds.bound(ord3, factory.setOf("0", "1", "2"));
        bounds.bound(first3, bounds.upperBound(ord3));
        bounds.bound(last3, bounds.upperBound(ord3));
        assertNotNull(solve(to3.product(ac1).some().and(ac1.acyclic()).and(to3.totalOrder(ord3, first3, last3))));
        assertPrimVarNum(bounds.upperBound(ac1).size());
    }

}
