/**
 *
 */
package tests.basic;

import java.util.Arrays;
import java.util.Iterator;

import examples.alloy.CeilingsAndFloors;
import examples.alloy.Dijkstra;
import junit.framework.TestCase;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.Universe;

/**
 * Tests the solution enumeration functionality of the Solver class.
 *
 * @author Emina Torlak
 */
public class EnumerationTest extends TestCase {

    private final Solver solver;

    /**
     * Constructs a new EnumerationTest.
     */
    public EnumerationTest(String arg0) {
        super(arg0);
        solver = new Solver();
        solver.options().setSolver(SATFactory.MiniSat);
    }

    public final void testCeilingsAndFloors() {
        final CeilingsAndFloors model = new CeilingsAndFloors();
        final Formula f = model.checkBelowTooAssertion();

        // has exactly one instance
        Iterator<Solution> sol = solver.solveAll(f, model.bounds(2, 2));
        assertNotNull(sol.next().instance());
        assertNull(sol.next().instance());
        assertFalse(sol.hasNext());

        // has more than one instance
        sol = solver.solveAll(f, model.bounds(3, 3));
        assertNotNull(sol.next().instance());
        assertNotNull(sol.next().instance());
        assertTrue(sol.hasNext());

        // has no instances
        sol = solver.solveAll(model.checkBelowTooDoublePrime(), model.bounds(3, 3));
        assertNull(sol.next().instance());
    }

    public final void testDijkstra() {
        final Dijkstra model = new Dijkstra();
        final Formula f = model.showDijkstra();

        Iterator<Solution> sol = solver.solveAll(f, model.bounds(5, 2, 2));
        // has more than one instance
        assertNotNull(sol.next().instance());
        assertNotNull(sol.next().instance());
        assertTrue(sol.hasNext());

    }

    public final void testTrivial() {
        final Relation r = Relation.unary("r");
        final Universe u = new Universe(Arrays.asList("a", "b", "c"));
        final TupleFactory f = u.factory();
        final Bounds b = new Bounds(u);
        b.bound(r, f.setOf("a"), f.allOf(1));
        final Formula someR = r.some();

        Iterator<Solution> sol = solver.solveAll(someR, b);
        // has a trivial instance, followed by 2 non-trivial instances
        assertEquals(Solution.Outcome.TRIVIALLY_SATISFIABLE, sol.next().outcome());
        assertEquals(Solution.Outcome.SATISFIABLE, sol.next().outcome());
        assertEquals(Solution.Outcome.SATISFIABLE, sol.next().outcome());
        assertEquals(Solution.Outcome.UNSATISFIABLE, sol.next().outcome());
        assertFalse(sol.hasNext());

    }

}
