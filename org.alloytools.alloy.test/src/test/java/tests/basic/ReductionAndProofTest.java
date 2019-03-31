package tests.basic;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import junit.framework.TestCase;
import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Node;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.ucore.ECFPStrategy;
import kodkod.engine.ucore.NCEStrategy;
import kodkod.instance.Bounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.Universe;
import kodkod.util.collections.IdentityHashSet;
import kodkod.util.nodes.Nodes;

/**
 * Tests the reduction algorithm for trivially (un)satisfiable formulas, and
 * does limited testing of core extraction.
 *
 * @author Emina Torlak
 */
public class ReductionAndProofTest extends TestCase {

    private final int          USIZE = 10;
    private final TupleFactory factory;
    private final Solver       solver;
    private final Relation     a, b, a2b, b2a;
    private final Relation     first, last, ordered, total;
    private final Bounds       bounds;

    public ReductionAndProofTest(String arg0) {
        super(arg0);
        this.solver = new Solver();
        solver.options().setLogTranslation(2);
        solver.options().setSolver(SATFactory.MiniSatProver);
        List<String> atoms = new ArrayList<String>(USIZE);
        for (int i = 0; i < USIZE; i++) {
            atoms.add("" + i);
        }
        final Universe universe = new Universe(atoms);
        this.factory = universe.factory();
        this.a = Relation.unary("a");
        this.b = Relation.unary("b");
        this.a2b = Relation.binary("a2b");
        this.b2a = Relation.binary("b2a");
        this.first = Relation.unary("first");
        this.last = Relation.unary("last");
        this.ordered = Relation.unary("ordered");
        this.total = Relation.binary("total");
        this.bounds = new Bounds(universe);
    }

    @Override
    protected void setUp() throws Exception {
        super.setUp();
        bounds.bound(a, factory.setOf("0", "1", "2", "3", "4"));
        bounds.bound(b, factory.setOf("5", "6", "7", "8", "9"));
        bounds.bound(a2b, bounds.upperBound(a).product(bounds.upperBound(b)));
        bounds.bound(b2a, bounds.upperBound(b).product(bounds.upperBound(a)));

        bounds.boundExactly(first, factory.setOf("0"));
        bounds.boundExactly(last, factory.setOf("4"));
        bounds.boundExactly(ordered, bounds.upperBound(a));
        bounds.boundExactly(total, factory.setOf(factory.tuple("0", "1"), factory.tuple("1", "2"), factory.tuple("2", "3"), factory.tuple("3", "4")));
    }

    private Set<Formula> reduce(Formula formula) {

        final Solution sol = solver.solve(formula, bounds);
        assertEquals(Solution.Outcome.TRIVIALLY_UNSATISFIABLE, sol.outcome());
        sol.proof().minimize(null);
        return Nodes.minRoots(formula, sol.proof().highLevelCore().values());

    }

    public final void testReduction() {
        Formula f0, f1, f2, f3, f4, f5, f6;

        f0 = a.difference(b).eq(a); // T
        assertEquals(Solution.Outcome.TRIVIALLY_SATISFIABLE, solver.solve(f0, bounds).outcome());

        f1 = a2b.join(b2a).some();
        assertEquals(Solution.Outcome.TRIVIALLY_SATISFIABLE, solver.solve(f0.or(f1), bounds).outcome());

        f2 = total.totalOrder(ordered, first, last);
        f3 = first.join(total).no(); // F

        Set<Formula> reduction = reduce(f3.and(f0).and(f1).and(f2));
        assertEquals(1, reduction.size());
        assertTrue(reduction.contains(f3));

        f4 = total.acyclic();
        f5 = total.closure().intersection(Expression.IDEN).some(); // F

        reduction = reduce(f4.and(f1).and(f0).and(f5));
        assertEquals(1, reduction.size());
        assertTrue(reduction.contains(f5));

        bounds.boundExactly(a2b, bounds.upperBound(a2b));
        bounds.boundExactly(a, bounds.upperBound(a));
        bounds.boundExactly(b, bounds.upperBound(b));
        f6 = a2b.function(a, b); // F

        reduction = reduce(f1.and(f2).and(f6));
        assertEquals(1, reduction.size());
        assertTrue(reduction.contains(f6));

    }

    public final void testProof() {
        Variable v0 = Variable.unary("v0"), v1 = Variable.unary("v1"), v2 = Variable.unary("v2");
        Formula f0 = v0.join(a2b).eq(v1.union(v2)).and(v1.eq(v2).not());
        Formula f1 = f0.forSome(v0.oneOf(a).and(v1.oneOf(b)).and(v2.oneOf(b)));
        Formula f2 = a2b.function(a, b);
        Formula f3 = f1.and(f2).and(total.totalOrder(ordered, first, last));

        Solution sol = null;

        solver.options().setLogTranslation(0);
        solver.options().setSolver(SATFactory.MiniSat);
        sol = solver.solve(f3, bounds);
        assertEquals(Solution.Outcome.UNSATISFIABLE, sol.outcome());
        assertNull(sol.proof());
        solver.options().setLogTranslation(1);
        sol = solver.solve(f3, bounds);
        assertNull(sol.proof());

        solver.options().setSolver(SATFactory.MiniSatProver);
        sol = solver.solve(f3, bounds);

        // System.out.println(f3 + ", " + bounds);

        sol.proof().minimize(new ECFPStrategy());
        final Set<Formula> top = Nodes.minRoots(f3, sol.proof().highLevelCore().values());
        assertEquals(2, top.size());
        assertTrue(top.contains(f1));
        assertTrue(top.contains(f2));
        // for(Iterator<TranslationLog.Record> itr = sol.proof().core();
        // itr.hasNext(); ) {
        // System.out.println(itr.next());
        // }

    }

    private Set<Node> reduce(Formula formula, int granularity) {
        solver.options().setCoreGranularity(granularity);
        final Solution sol = solver.solve(formula, bounds);
        assertEquals(Solution.Outcome.TRIVIALLY_UNSATISFIABLE, sol.outcome());
        sol.proof().minimize(null);
        return new IdentityHashSet<Node>(sol.proof().highLevelCore().values());

    }

    private Set<Node> core(Formula formula, int granularity) {
        solver.options().setCoreGranularity(granularity);
        final Solution sol = solver.solve(formula, bounds);
        assertEquals(Solution.Outcome.UNSATISFIABLE, sol.outcome());
        sol.proof().minimize(new NCEStrategy(sol.proof().log()));
        return new IdentityHashSet<Node>(sol.proof().highLevelCore().values());

    }

    public final void testGranularity() {
        final Variable x = Variable.unary("x");
        final Variable y = Variable.unary("y");

        final Formula f0 = a.some();
        final Formula f1 = b.some();
        final Formula f2 = a.eq(b);

        final Formula f3 = x.product(y).in(Expression.UNIV.product(Expression.UNIV));
        final Formula f4 = x.eq(y);

        final Formula f5 = f3.or(f4).forSome(y.oneOf(b));
        final Formula f6 = f5.forAll(x.oneOf(a));

        final Formula f7 = f2.or(f6).not();

        final Formula f8 = b.intersection(Expression.UNIV).some();

        final Formula f9 = Formula.and(f0, f1, f7, f8);

        Set<Node> core = core(f9, 0);
        assertEquals(2, core.size());
        assertTrue(core.contains(f1));
        assertTrue(core.contains(f7));

        core = core(f9, 1);
        assertEquals(2, core.size());
        assertTrue(core.contains(f1));
        assertTrue(core.contains(f6));

        core = reduce(f9, 2);
        assertEquals(2, core.size());
        assertTrue(core.contains(f1));
        assertTrue(core.contains(f5));

        core = core(f9, 3);
        assertEquals(2, core.size());
        assertTrue(core.contains(f1));
        assertTrue(core.contains(f3));
    }

}
