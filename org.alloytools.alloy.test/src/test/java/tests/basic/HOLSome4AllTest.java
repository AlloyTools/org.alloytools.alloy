package tests.basic;

import java.util.LinkedList;
import java.util.List;

import org.junit.Test;

import junit.framework.TestCase;
import kodkod.ast.Decl;
import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.IntConstant;
import kodkod.ast.IntExpression;
import kodkod.ast.QuantifiedFormula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.Evaluator;
import kodkod.engine.HOLSolver;
import kodkod.engine.Solution;
import kodkod.engine.config.Options;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

//FIXED: tests are failing because atom relations are not automatically created
//TODO: add this test
// for x: X | some set s: S | ...
public class HOLSome4AllTest extends TestCase {

    private static final IntConstant M1 = IntConstant.constant(-1);
    private static final IntConstant I0 = IntConstant.constant(0);
    private static final IntConstant I1 = IntConstant.constant(1);
    private static final IntConstant I2 = IntConstant.constant(2);
    private static final IntConstant I3 = IntConstant.constant(3);

    protected Bounds                 bounds;
    protected Options                options;
    protected Universe               universe;
    protected TupleFactory           factory;

    protected Relation               Node;
    protected Relation               S;
    protected Variable               s;
    protected IntExpression          si;
    protected Variable               ns;

    protected int bw() {
        return 5;
    }

    @Override
    protected void setUp() throws Exception {
        super.setUp();
        createRelations();
        createBounds();
        setupOptions();
    }

    @Test
    public void testE1() {
        // SAT: some s: ints | all ns: set Node | #ns > s
        Formula f = ns.count().gt(si).forAll(ns.setOf(Node)).forSome(s.oneOf(Expression.INTS));
        Solution sol = solve(f);
        assertEquals(true, sol.sat());
        assertEquals(-1, evalS(sol));
    }

    @Test
    public void testE1i() {
        // SAT: some s: ints | all s: set Node | #s > s
        Variable ns = Variable.unary("s");
        Formula f = ns.count().gt(si).forAll(ns.setOf(Node)).forSome(s.oneOf(Expression.INTS));
        Solution sol = solve(f);
        assertEquals(true, sol.sat());
        assertEquals(-1, evalS(sol));
    }

    @Test
    public void testE1ii() {
        // SAT: some s: ints | all $s: set Node | #$s > s
        Variable ns = Variable.unary("$s");
        Formula f = ns.count().gt(si).forAll(ns.setOf(Node)).forSome(s.oneOf(Expression.INTS));
        Solution sol = solve(f);
        assertEquals(true, sol.sat());
        assertEquals(-1, evalS(sol));
    }

    @Test
    public void testE2() {
        // UNSAT: some s: ints | s > 0 && (all ns: set Node | #ns > s)
        Formula cnd = si.gt(I0);
        Formula f = cnd.and(ns.count().gt(si).forAll(ns.setOf(Node))).forSome(s.oneOf(Expression.INTS));
        Solution sol = solve(f);
        assertEquals(false, sol.sat());
    }

    @Test
    public void testE3() {
        // SAT: some s: ints | s > 0 && (all ns: set Node | some ns => #ns > s)
        Formula cnd = si.gt(I0);
        Formula f = cnd.and(ns.some().implies(ns.count().gt(si)).forAll(ns.setOf(Node))).forSome(s.oneOf(Expression.INTS));
        Solution sol = solve(f);
        assertTrue(sol.sat());
        assertEquals(0, eval(sol, Node).size());
    }

    @Test
    public void testE4() {
        // UNSAT: some Node && some s: ints | s > 0 && (all ns: set Node | some
        // ns => #ns > s)
        Formula cnd = si.gt(I0);
        Formula f = Node.some().and(cnd.and(ns.some().implies(ns.count().gt(si)).forAll(ns.setOf(Node))).forSome(s.oneOf(Expression.INTS)));
        Solution sol = solve(f);
        assertFalse(sol.sat());
    }

    @Test
    public void testE4i() {
        // UNSAT: some Node &&
        // all n: Node | some n &&
        // some s: ints | s > 0 && (all ns: set Node | some ns => #ns > s)
        Variable n = Variable.unary("n");
        Formula cnd = si.gt(I0);
        Formula f = Formula.and(Node.some(), n.some().forAll(n.oneOf(Node)), cnd.and(ns.some().implies(ns.count().gt(si)).forAll(ns.setOf(Node))).forSome(s.oneOf(Expression.INTS)));
        Solution sol = solve(f);
        assertFalse(sol.sat());
    }

    @Test
    public void testE5() {
        // SAT: some Node && some s: ints | s >= 0 && (all ns: set Node | some
        // ns => #ns > s)
        Formula cnd = si.gte(I0);
        Formula f = Node.some().and(cnd.and(ns.some().implies(ns.count().gt(si)).forAll(ns.setOf(Node))).forSome(s.oneOf(Expression.INTS)));
        Solution sol = solve(f);
        assertEquals(true, sol.sat());
        assertEquals(0, evalS(sol));
    }

    @Test
    public void testE6() {
        // SAT: some s: ints |
        // s > 1 || (all ns: set Node | #ns > s)
        Formula cnd = si.gt(I1);
        Formula f = cnd.or(ns.count().gt(si).forAll(ns.setOf(Node))).forSome(s.oneOf(Expression.INTS));
        Solution sol = solve(f);
        assertTrue(sol.sat());
    }

    @Test
    public void testE7() {
        // SAT: some s: ints |
        // s > 3 || (all ns: set Node | #ns > s)
        Formula cnd = si.gt(I3);
        QuantifiedFormula allQF = (QuantifiedFormula) ns.count().gt(si).forAll(ns.setOf(Node));
        Decl someDecls = s.oneOf(Expression.INTS);
        {
            Formula f = cnd.or(allQF).forSome(someDecls);
            Solution sol = solve(f);
            assertTrue(sol.sat());
            assertEquals(-1, evalS(sol));
        }
        {
            Formula f = cnd.or(flip(allQF)).forSome(someDecls);
            Solution sol = solve(f);
            assertTrue(sol.sat());
            assertEquals(-1, evalS(sol));
        }
    }

    @Test
    public void testE8() {
        // UNSAT: some s: ints - (-1) |
        // s > 3 || (all ns: set Node | #ns > s)
        Formula cnd = si.gt(I3);
        QuantifiedFormula allQF = (QuantifiedFormula) ns.count().gt(si).forAll(ns.setOf(Node));
        Decl someDecls = s.oneOf(Expression.INTS.difference(M1.toExpression()));
        {
            Formula f = cnd.or(allQF).forSome(someDecls);
            assertFalse(solve(f).sat());
        }
        // same thing, but inner flipped
        // UNSAT: some s: ints - (-1) |
        // s > 3 || (all ns: set Node | #ns > s)
        {
            Formula f = cnd.or(flip(allQF)).forSome(someDecls);
            assertFalse(solve(f).sat());
        }
    }

    @Test
    public void testE9() {
        // UNSAT: some s: ints - (-1) |
        // s > 3 || (some ns: set Node | #ns > s + 3)
        Formula cnd = si.gt(I3);
        QuantifiedFormula innerSomeQF = (QuantifiedFormula) ns.count().gt(si.plus(I3)).forSome(ns.setOf(Node));
        Decl someDecls = s.oneOf(Expression.INTS.difference(M1.toExpression()));
        Formula f = cnd.or(innerSomeQF).forSome(someDecls);
        assertFalse(solve(f).sat());
    }

    @Test
    public void testE9i() {
        // SAT: some s: ints |
        // s > 3 || (some ns: set Node | #ns > s + 3)
        Formula cnd = si.gt(I3);
        QuantifiedFormula innerSomeQF = (QuantifiedFormula) ns.count().gt(si.plus(I3)).forSome(ns.setOf(Node));
        Decl someDecls = s.oneOf(Expression.INTS);
        Formula f = cnd.or(innerSomeQF).forSome(someDecls);
        Solution sol = solve(f);
        assertTrue(sol.sat());
        assertEquals(-1, evalS(sol));
    }

    @Test
    public void testE9ii() {
        // SAT: some s: ints - 1 |
        // s > 2 || (some ns: set Node | #ns > s + 3)
        Formula cnd = si.gt(I2);
        QuantifiedFormula innerSomeQF = (QuantifiedFormula) ns.count().gt(si.plus(I3)).forSome(ns.setOf(Node));
        Decl someDecls = s.oneOf(Expression.INTS.difference(M1.toExpression()));
        Formula f = cnd.or(innerSomeQF).forSome(someDecls);
        Solution sol = solve(f);
        assertTrue(sol.sat());
        assertEquals(3, evalS(sol));
    }

    @Test
    public void testParallel1() {
        doTestParallel1(Variable.unary("ns2"));
        doTestParallel1(Variable.unary("ns"));
    }

    @Test
    public void testParallel1i() {
        doTestParallel1i(Variable.unary("ns2"));
        doTestParallel1i(Variable.unary("ns"));
    }

    @Test
    public void testSome4AllLone() {
        // SAT:
        // pred P { some s: Node | all p: lone Node | #s >= #p }
        // check { P <=> P }
        Variable vs = Variable.unary("s");
        Variable vp = Variable.unary("p");
        Formula f = vs.count().gte(vp.count()).forAll(vp.loneOf(Node)).forSome(vs.oneOf(Node));
        Solution sol = solve(f.iff(f).not());
        assertFalse(sol.sat());
    }

    private void doTestParallel1(Variable ns2) {
        // SAT: some s: ints {
        // all ns: set Node | #ns > s
        // all ns2: set Node | #ns2 > s
        // }
        Formula h1 = ns.count().gt(si).forAll(ns.setOf(Node));
        Formula h2 = ns2.count().gt(si).forAll(ns2.setOf(Node));
        Formula f = h1.and(h2).forSome(s.oneOf(Expression.INTS));
        Solution sol = solve(f);
        assertTrue(sol.sat());
        assertEquals(-1, evalS(sol));
    }

    private void doTestParallel1i(Variable ns2) {
        // UNSAT: some s: ints {
        // s > 0
        // all ns: set Node | #ns > s
        // all ns2: set Node | #ns2 > s
        // }
        Formula h1 = ns.count().gt(si).forAll(ns.setOf(Node));
        Formula h2 = ns2.count().gt(si).forAll(ns2.setOf(Node));
        Formula f = h1.and(h2).and(si.gt(I0)).forSome(s.oneOf(Expression.INTS));
        assertFalse(solve(f).sat());
    }

    public void testParallel2() {
        // UNSAT: some s: ints {
        // all ns: set Node | #ns > s
        // all ns2: set Node | #ns2 < s
        // }
        Variable ns2 = Variable.unary("ns2");
        Formula h1 = ns.count().gt(si).forAll(ns.setOf(Node));
        Formula h2 = ns2.count().lt(si).forAll(ns2.setOf(Node));
        Formula f = h1.and(h2).forSome(s.oneOf(Expression.INTS));
        assertFalse(solve(f).sat());
    }

    @Test
    public void testA1() {
        // SAT: all s: ints | s < 0 => (all ns: set Node | #ns > s)
        Formula f = si.lt(I0).implies(ns.count().gt(si).forAll(ns.setOf(Node))).forAll(s.oneOf(Expression.INTS));
        Solution sol = solve(f);
        assertTrue(sol.sat());
    }

    protected int evalS(Solution sol) {
        Instance inst = sol.instance();
        TupleSet x = inst.tuples(inst.skolems().iterator().next());
        return (Integer) x.iterator().next().atom(0);
    }

    protected int eval(Solution sol, IntExpression ie) {
        Evaluator ev = new Evaluator(sol.instance());
        return ev.evaluate(ie);
    }

    protected TupleSet eval(Solution sol, Expression e) {
        Evaluator ev = new Evaluator(sol.instance());
        return ev.evaluate(e);
    }

    protected Solution solve(Formula f) {
        HOLSolver s = HOLSolver.solver(options);
        return s.solve(f, bounds);
    }

    private void createRelations() {
        Node = Relation.unary("Node");
        S = Relation.unary("$S");
        s = Variable.unary("s");
        si = s.sum();
        ns = Variable.unary("ns");
    }

    private Universe getUniverse() {
        List<Object> atoms = new LinkedList<Object>();
        atoms.add("Node1");
        atoms.add("Node2");
        atoms.add("Node3");
        atoms.add(-1);
        atoms.add(0);
        atoms.add(1);
        atoms.add(2);
        atoms.add(3);
        return new Universe(atoms);
    }

    private void createBounds() {
        universe = getUniverse();
        factory = universe.factory();
        bounds = new Bounds(universe);
        bounds.bound(Node, factory.setOf("Node1", "Node2", "Node3"));
        bounds.boundExactly(-1, factory.setOf(-1));
        bounds.boundExactly(0, factory.setOf(0));
        bounds.boundExactly(1, factory.setOf(1));
        bounds.boundExactly(2, factory.setOf(2));
        bounds.boundExactly(3, factory.setOf(3));
        bounds.bound(S, factory.noneOf(1), factory.setOf(-1, 0, 1, 2, 3));
    }

    protected void setupOptions() {
        options = new Options();
        options.setNoOverflow(true);
        options.setBitwidth(bw());
        options.setSolver(SATFactory.MiniSat);
        options.setAllowHOL(true);
    }

    private Formula flip(QuantifiedFormula qf) {
        return qf.formula().not().quantify(qf.quantifier().opposite, qf.decls()).not();
    }

    public static void main(String[] args) throws Exception {
        HOLSome4AllTest t = new HOLSome4AllTest();
        t.setUp();
        // t._testTmp();
        // t.testE9ii();
        // t._testA1();
        t.testParallel2();
    }

}
