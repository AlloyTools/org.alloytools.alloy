package tests.basic;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import junit.framework.TestCase;
import kodkod.ast.Decl;
import kodkod.ast.Decls;
import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.ast.operator.Multiplicity;
import kodkod.engine.Solver;
import kodkod.engine.fol2sat.HigherOrderDeclException;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;
import kodkod.instance.TupleFactory;
import kodkod.instance.Universe;

/**
 * Tests skolemization.
 */
public class SkolemizationTest extends TestCase {

    private final int          USIZE = 10;
    private final TupleFactory factory;
    private final Solver       solver;
    private final Relation     r1a, r1b, r2a, r2b;
    private final Bounds       bounds;

    public SkolemizationTest(String arg0) {
        super(arg0);
        this.solver = new Solver();
        List<String> atoms = new ArrayList<String>(USIZE);
        for (int i = 0; i < USIZE; i++) {
            atoms.add("" + i);
        }
        final Universe universe = new Universe(atoms);
        this.factory = universe.factory();
        this.r1a = Relation.unary("r1a");
        this.r1b = Relation.unary("r1b");
        this.r2a = Relation.binary("r2a");
        this.r2b = Relation.binary("r2b");
        this.bounds = new Bounds(universe);
    }

    @Override
    protected void setUp() throws Exception {
        super.setUp();
        bounds.bound(r1a, factory.setOf("0", "1", "2", "3", "4"));
        bounds.bound(r1b, factory.setOf("5", "6", "7", "8", "9"));
        bounds.bound(r2a, bounds.upperBound(r1a).product(bounds.upperBound(r1b)));
        bounds.bound(r2b, bounds.upperBound(r1b).product(bounds.upperBound(r1a)));
    }

    private Instance solve(Formula formula) {

        return solver.solve(formula, bounds).instance();

    }

    private final void testNoSkolems(Decls d, Formula f) {
        Instance inst = solve(f.not());
        assertEquals(bounds.relations(), inst.relations());

        inst = solve(f.or(r2a.in(r2b)));
        assertEquals(bounds.relations(), inst.relations());

        inst = solve(f.iff(r2a.in(r2b)));
        assertEquals(bounds.relations(), inst.relations());

        inst = solve(r2a.in(r2b).implies(f));
        assertEquals(bounds.relations(), inst.relations());

    }

    private final void testNoSkolems(Multiplicity mult) {
        final Variable v = Variable.unary("v");
        final Decl d = v.declare(mult, r1a);

        testNoSkolems(d, v.join(r2a).some().forAll(d).not());
        testNoSkolems(d, v.join(r2a).some().forSome(d));

    }

    public final void testNoSkolems() {
        testNoSkolems(Multiplicity.ONE);
        try {
            testNoSkolems(Multiplicity.LONE);
            fail();
        } catch (HigherOrderDeclException hode) {}
        try {
            testNoSkolems(Multiplicity.SOME);
            fail();
        } catch (HigherOrderDeclException hode) {}
        try {
            testNoSkolems(Multiplicity.SET);
            fail();
        } catch (HigherOrderDeclException hode) {}
    }

    private final void assertSkolems(Bounds bounds, Instance inst, Set<String> skolems) {
        assertEquals(skolems.size(), inst.relations().size() - bounds.relations().size());
        for (Relation r : inst.relations()) {
            assertTrue(skolems.contains(r.name()) || bounds.relations().contains(r));
        }
    }

    private final void testSkolems(Multiplicity mult) {
        final Variable va = Variable.unary("va");
        final Variable vb = Variable.unary("vb");
        final Set<String> skolems = new HashSet<String>(4);

        Decl da = va.declare(mult, r1a);
        Decl db = vb.declare(mult, r1b);

        skolems.add("$" + va.name());

        Instance inst = solve(va.in(r1b.join(r2b)).forAll(da).not());
        assertSkolems(bounds, inst, skolems);

        inst = solve((r2b.some().implies(va.in(r1b.join(r2b)).forAll(da))).not());
        assertSkolems(bounds, inst, skolems);

        inst = solve(va.in(r1b.join(r2b)).forSome(da));
        assertSkolems(bounds, inst, skolems);

        inst = solve(va.in(r1b.join(r2b)).forSome(da).and(va.in(r1b).not().forAll(mult == Multiplicity.ONE ? da : va.oneOf(r1a))));
        assertSkolems(bounds, inst, skolems);
        final Expression e0 = va.join(r2a);
        final Formula f0 = e0.some().forSome(va.oneOf(r1a));
        final Formula f1 = e0.no().forAll(va.oneOf(r2a.join(r1b)));

        inst = solve(f0.and(f1));
        assertSkolems(bounds, inst, skolems);

        skolems.add("$" + vb.name());

        inst = solve(va.in(vb.join(r2b)).forSome(da.and(vb.oneOf(va.join(r2a)))));
        assertSkolems(bounds, inst, skolems);

        inst = solve((va.in(vb.join(r2b)).forAll(vb.oneOf(va.join(r2a))).forAll(da)).not());
        assertSkolems(bounds, inst, skolems);

        inst = solve(va.in(vb.join(r2b)).forAll(da.and(db)).not());
        assertSkolems(bounds, inst, skolems);

        inst = solve(va.in(vb.join(r2b)).forSome(da.and(db)));
        assertSkolems(bounds, inst, skolems);

        inst = solve(va.in(r1b.join(r2b)).forSome(da).and(r1b.in(vb).forAll(db).not()));
        assertSkolems(bounds, inst, skolems);

    }

    public final void testSkolems() {
        testSkolems(Multiplicity.ONE);
        testSkolems(Multiplicity.LONE);
        testSkolems(Multiplicity.SOME);
        testSkolems(Multiplicity.SET);
    }

    private final void testDeepSkolems(Multiplicity mult) {
        final Variable va = Variable.unary("va");
        final Variable vb = Variable.unary("vb");
        final Variable vc = Variable.unary("vc");
        final Variable vd = Variable.unary("vd");
        final Set<String> skolems = new HashSet<String>(4);

        Decl da1 = va.oneOf(r1a);
        Decl db = vb.declare(mult, r1b);
        Decl dc = vc.declare(mult, r1a);
        Decl dc1 = vc.oneOf(r1a);
        Decl dd = vd.declare(mult, r1b);
        Decl dd1 = vd.oneOf(r1b);

        skolems.add("$" + vb.name());

        Instance inst = solve(va.in(vb.join(r2b)).forSome(db).forAll(da1));
        assertSkolems(bounds, inst, skolems);

        skolems.add("$" + vc.name());
        inst = solve(va.in(vb.join(r2b).union(vd.join(r2b)).union(vc)).forSome(db).forAll(da1).forSome(dc).forAll(dd1));
        assertSkolems(bounds, inst, skolems);

        inst = solve(va.in(vb.join(r2b).union(vd.join(r2b)).union(vc)).forSome(db).forSome(dc).forAll(da1.and(dd1)));
        assertSkolems(bounds, inst, skolems);

        skolems.add("$" + vd.name());
        inst = solve(va.in(vb.join(r2b).union(vd.join(r2b)).union(vc)).forSome(db).forAll(da1).forSome(dc).not().forAll(dd).not());

        assertSkolems(bounds, inst, skolems);

        inst = solve(va.in(vb.join(r2b).union(vd.join(r2b)).union(vc)).forAll(dc).forAll(db).forSome(da1).not().forAll(dd1));
        skolems.remove("$" + vd.name());
        assertSkolems(bounds, inst, skolems);

        inst = solve(va.in(vb.join(r2b).union(vd.join(r2b)).union(vc)).forSome(db).forAll(dc1).forAll(da1).forAll(dd1));
        skolems.remove("$" + vc.name());
        assertSkolems(bounds, inst, skolems);

    }

    public final void testDeepSkolems() {
        solver.options().setSkolemDepth(3);
        testDeepSkolems(Multiplicity.ONE);
        testDeepSkolems(Multiplicity.LONE);
        testDeepSkolems(Multiplicity.SOME);
        testDeepSkolems(Multiplicity.SET);
        final Variable va = Variable.unary("va");
        final Variable vb = Variable.unary("vb");
        Decl da1 = va.oneOf(r1a);
        Decl db = vb.oneOf(r1b);
        final Formula f0 = va.in(vb.join(r2b));
        final Formula f1 = f0.forAll(db).not().forAll(da1);
        final Formula f2 = f0.forSome(db).forSome(da1);
        Instance inst = solve(f1.and(f2));
        assertEquals(bounds.relations().size() + 3, inst.relations().size());
    }
}
