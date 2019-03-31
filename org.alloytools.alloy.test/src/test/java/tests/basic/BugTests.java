package tests.basic;

import static kodkod.ast.Expression.UNIV;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import junit.framework.TestCase;
import kodkod.ast.Decl;
import kodkod.ast.Decls;
import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.IntConstant;
import kodkod.ast.IntExpression;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.Evaluator;
import kodkod.engine.Proof;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.config.AbstractReporter;
import kodkod.engine.config.Options;
import kodkod.engine.fol2sat.HigherOrderDeclException;
import kodkod.engine.fol2sat.Translator;
import kodkod.engine.fol2sat.UnboundLeafException;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.ucore.RCEStrategy;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;
import kodkod.instance.Tuple;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;
import kodkod.util.ints.IntBitSet;
import kodkod.util.ints.IntIterator;
import kodkod.util.ints.IntSet;
import kodkod.util.ints.IntTreeSet;
import kodkod.util.nodes.Nodes;

/**
 * Test cases that record reported bugs.
 *
 * @author Emina Torlak
 */
public class BugTests extends TestCase {

    private final Solver solver = new Solver();

    public final void testBGP_03172011() {

        Relation x5 = Relation.unary("s012");
        Relation x8 = Relation.unary("zero");
        Relation x9 = Relation.unary("one");
        Relation x12 = Relation.nary("next", 2);

        Universe universe = new Universe(Arrays.asList("0", "1", "2", "3"));
        TupleFactory factory = universe.factory();
        Bounds bounds = new Bounds(universe);

        bounds.boundExactly(x5, factory.setOf("0", "1", "2"));
        bounds.boundExactly(x8, factory.setOf("0"));
        bounds.bound(x9, factory.setOf("1"), factory.setOf("1", "2"));

        TupleSet x12_upper = factory.noneOf(2);
        x12_upper.add(factory.tuple("1", "2"));
        x12_upper.add(factory.tuple("2", "3"));
        bounds.boundExactly(x12, x12_upper);

        Variable x714 = Variable.unary("x714");
        Decls x713 = x714.oneOf(x8.union(x9));

        Variable x720 = Variable.unary("x720");
        Expression x723 = x8.union(x9);
        Expression x724 = x9.join(x12);
        Expression x722 = x723.union(x724);
        Expression x721 = x722.difference(x714);
        Decls x719 = x720.oneOf(x721);

        Variable x727 = Variable.unary("x727");
        Expression x732 = x714.union(x720);
        Expression x728 = x5.difference(x732);
        Decls x726 = x727.oneOf(x728);

        Variable x735 = Variable.unary("x735");
        Decls x734 = x735.oneOf(x8);

        Variable x893 = Variable.unary("x893");
        Decls x892 = x893.oneOf(x727);
        Formula x894 = x720.no();
        Formula x891 = x894.forAll(x892);

        Formula x712 = x891.forSome(x713.and(x719).and(x726).and(x734));
        Formula x267 = Formula.FALSE.or(x712);

        Solver solver = new Solver();
        solver.options().setSolver(SATFactory.MiniSat);
        solver.options().setBitwidth(4);
        // solver.options().setFlatten(false);
        solver.options().setIntEncoding(Options.IntEncoding.TWOSCOMPLEMENT);
        solver.options().setSymmetryBreaking(20);
        solver.options().setSkolemDepth(0);

        final Solution sol = solver.solve(x267, bounds);
        assertEquals(sol.outcome(), Solution.Outcome.TRIVIALLY_UNSATISFIABLE);
    }

    public final void testFelix_03162009() {
        Relation x = Relation.unary("X");
        Relation y = Relation.unary("Y");
        Relation q = Relation.unary("Q");
        Relation f = Relation.nary("f", 2);

        List<String> atomlist = Arrays.asList("X", "Y");

        Universe universe = new Universe(atomlist);
        TupleFactory factory = universe.factory();
        Bounds bounds = new Bounds(universe);

        TupleSet x_upper = factory.noneOf(1);
        x_upper.add(factory.tuple("X"));
        bounds.boundExactly(x, x_upper);

        TupleSet y_upper = factory.noneOf(1);
        y_upper.add(factory.tuple("Y"));
        bounds.boundExactly(y, y_upper);

        TupleSet q_upper = factory.noneOf(1);
        q_upper.add(factory.tuple("X"));
        q_upper.add(factory.tuple("Y"));
        bounds.bound(q, q_upper);

        TupleSet f_upper = factory.noneOf(2);
        f_upper.add(factory.tuple("X").product(factory.tuple("X")));
        f_upper.add(factory.tuple("X").product(factory.tuple("Y")));
        f_upper.add(factory.tuple("Y").product(factory.tuple("X")));
        f_upper.add(factory.tuple("Y").product(factory.tuple("Y")));
        bounds.bound(f, f_upper);

        Solver solver = new Solver();
        solver.options().setSolver(SATFactory.DefaultSAT4J);
        solver.options().setBitwidth(4);
        // solver.options().setFlatten(false);
        solver.options().setIntEncoding(Options.IntEncoding.TWOSCOMPLEMENT);
        solver.options().setSymmetryBreaking(20);
        solver.options().setSkolemDepth(0);

        Expression test = f.override(q.product(y));
        TupleSet approx = factory.setOf(test.arity(), Translator.approximate(test, bounds, solver.options()).denseIndices());
        assertEquals(f_upper, approx);
    }

    public final void testFelix_10272008() {
        Relation x0 = Relation.unary("Int/min");
        Relation x1 = Relation.unary("Int/zero");
        Relation x2 = Relation.unary("Int/max");
        Relation x3 = Relation.nary("Int/next", 2);
        Relation x4 = Relation.unary("seq/Int");
        Relation x5 = Relation.unary("this/X");

        List<String> atomlist = Arrays.asList("-1", "-2", "-3", "-4", "-5", "-6", "-7", "-8", "0", "1", "2", "3", "4", "5", "6", "7", "unused0", "unused1", "unused2");

        Universe universe = new Universe(atomlist);
        TupleFactory factory = universe.factory();
        Bounds bounds = new Bounds(universe);

        TupleSet x0_upper = factory.noneOf(1);
        x0_upper.add(factory.tuple("-8"));
        bounds.boundExactly(x0, x0_upper);

        TupleSet x1_upper = factory.noneOf(1);
        x1_upper.add(factory.tuple("0"));
        bounds.boundExactly(x1, x1_upper);

        TupleSet x2_upper = factory.noneOf(1);
        x2_upper.add(factory.tuple("7"));
        bounds.boundExactly(x2, x2_upper);

        TupleSet x3_upper = factory.noneOf(2);
        x3_upper.add(factory.tuple("-8").product(factory.tuple("-7")));
        x3_upper.add(factory.tuple("-7").product(factory.tuple("-6")));
        x3_upper.add(factory.tuple("-6").product(factory.tuple("-5")));
        x3_upper.add(factory.tuple("-5").product(factory.tuple("-4")));
        x3_upper.add(factory.tuple("-4").product(factory.tuple("-3")));
        x3_upper.add(factory.tuple("-3").product(factory.tuple("-2")));
        x3_upper.add(factory.tuple("-2").product(factory.tuple("-1")));
        x3_upper.add(factory.tuple("-1").product(factory.tuple("0")));
        x3_upper.add(factory.tuple("0").product(factory.tuple("1")));
        x3_upper.add(factory.tuple("1").product(factory.tuple("2")));
        x3_upper.add(factory.tuple("2").product(factory.tuple("3")));
        x3_upper.add(factory.tuple("3").product(factory.tuple("4")));
        x3_upper.add(factory.tuple("4").product(factory.tuple("5")));
        x3_upper.add(factory.tuple("5").product(factory.tuple("6")));
        x3_upper.add(factory.tuple("6").product(factory.tuple("7")));
        bounds.boundExactly(x3, x3_upper);

        TupleSet x4_upper = factory.noneOf(1);
        x4_upper.add(factory.tuple("0"));
        x4_upper.add(factory.tuple("1"));
        x4_upper.add(factory.tuple("2"));
        x4_upper.add(factory.tuple("3"));
        bounds.boundExactly(x4, x4_upper);

        TupleSet x5_upper = factory.noneOf(1);
        x5_upper.add(factory.tuple("unused0"));
        x5_upper.add(factory.tuple("unused1"));
        x5_upper.add(factory.tuple("unused2"));
        bounds.bound(x5, x5_upper);

        bounds.boundExactly(-8, factory.range(factory.tuple("-8"), factory.tuple("-8")));
        bounds.boundExactly(-7, factory.range(factory.tuple("-7"), factory.tuple("-7")));
        bounds.boundExactly(-6, factory.range(factory.tuple("-6"), factory.tuple("-6")));
        bounds.boundExactly(-5, factory.range(factory.tuple("-5"), factory.tuple("-5")));
        bounds.boundExactly(-4, factory.range(factory.tuple("-4"), factory.tuple("-4")));
        bounds.boundExactly(-3, factory.range(factory.tuple("-3"), factory.tuple("-3")));
        bounds.boundExactly(-2, factory.range(factory.tuple("-2"), factory.tuple("-2")));
        bounds.boundExactly(-1, factory.range(factory.tuple("-1"), factory.tuple("-1")));
        bounds.boundExactly(0, factory.range(factory.tuple("0"), factory.tuple("0")));
        bounds.boundExactly(1, factory.range(factory.tuple("1"), factory.tuple("1")));
        bounds.boundExactly(2, factory.range(factory.tuple("2"), factory.tuple("2")));
        bounds.boundExactly(3, factory.range(factory.tuple("3"), factory.tuple("3")));
        bounds.boundExactly(4, factory.range(factory.tuple("4"), factory.tuple("4")));
        bounds.boundExactly(5, factory.range(factory.tuple("5"), factory.tuple("5")));
        bounds.boundExactly(6, factory.range(factory.tuple("6"), factory.tuple("6")));
        bounds.boundExactly(7, factory.range(factory.tuple("7"), factory.tuple("7")));

        Variable x11 = Variable.unary("c");
        Expression x12 = x5.difference(x5);
        Decls x10 = x11.oneOf(x12);
        IntExpression x13 = IntConstant.constant(0);
        IntExpression x9 = x13.sum(x10);
        IntExpression x14 = IntConstant.constant(0);
        Formula x8 = x9.eq(x14);
        Formula x17 = x0.eq(x0);
        Formula x18 = x2.eq(x2);
        Formula x16 = x17.and(x18);
        Formula x19 = x3.eq(x3);
        Formula x15 = x16.and(x19);
        Formula x7 = x8.and(x15);
        Formula x22 = x1.eq(x1);
        Formula x23 = x4.eq(x4);
        Formula x21 = x22.and(x23);
        Formula x24 = x5.eq(x5);
        Formula x20 = x21.and(x24);
        Formula x6 = x7.and(x20);

        Solver solver = new Solver();
        solver.options().setSolver(SATFactory.DefaultSAT4J);
        solver.options().setBitwidth(4);
        // solver.options().setFlatten(false);
        solver.options().setIntEncoding(Options.IntEncoding.TWOSCOMPLEMENT);
        solver.options().setSymmetryBreaking(20);
        solver.options().setSkolemDepth(0);

        Solution sol = solver.solve(x6, bounds);
        assertEquals(sol.outcome(), Solution.Outcome.TRIVIALLY_SATISFIABLE);
    }

    public final void testFelix_06192008() {
        Relation x5 = Relation.unary("R");

        List<String> atomlist = Arrays.asList("X");

        Universe universe = new Universe(atomlist);
        TupleFactory factory = universe.factory();
        Bounds bounds = new Bounds(universe);

        TupleSet x5_upper = factory.noneOf(1);
        x5_upper.add(factory.tuple("X"));
        bounds.bound(x5, x5_upper);

        Variable x10 = Variable.unary("a");
        Expression x11 = x5.difference(x5);
        Decls x9 = x10.oneOf(x11);
        Variable x14 = Variable.nary("b", 2);
        Expression x15 = x5.product(x5);
        Decls x13 = x14.setOf(x15);
        Expression x19 = x5.product(x5);
        Formula x17 = x14.in(x19);
        Expression x22 = x10.product(x10);
        Formula x21 = x22.eq(x14);
        Formula x16 = x17.and(x21);
        Formula x12 = x16.forSome(x13);
        Formula x7 = x12.forAll(x9);

        // System.out.println(x7);

        Solver solver = new Solver();
        solver.options().setSolver(SATFactory.DefaultSAT4J);
        solver.options().setBitwidth(4);
        // solver.options().setFlatten(false);
        solver.options().setIntEncoding(Options.IntEncoding.TWOSCOMPLEMENT);
        solver.options().setSymmetryBreaking(20);

        // System.out.println("Depth=0..."); System.out.flush();
        solver.options().setSkolemDepth(0);
        assertEquals(Solution.Outcome.TRIVIALLY_SATISFIABLE, solver.solve(x7, bounds).outcome());

        // System.out.println("Depth=1..."); System.out.flush();
        solver.options().setSkolemDepth(1);
        final Solution sol = solver.solve(x7, bounds);
        assertEquals(Solution.Outcome.SATISFIABLE, sol.outcome());
        assertEquals(2, sol.instance().relations().size());
        for (Relation r : sol.instance().relations()) {
            assertTrue(sol.instance().tuples(r).isEmpty());
        }
    }

    public final void testFelix_05072008() {
        Relation A = Relation.unary("A"), first = Relation.unary("OrdFirst"), last = Relation.unary("OrdLast"),
                        next = Relation.nary("OrdNext", 2);

        List<String> atomlist = Arrays.asList("A1", "A2", "A3");
        Universe universe = new Universe(atomlist);
        TupleFactory factory = universe.factory();
        Bounds bounds = new Bounds(universe);

        TupleSet all = factory.setOf("A1", "A2", "A3");
        bounds.boundExactly(A, all);
        bounds.bound(first, all);
        bounds.bound(last, all);
        bounds.bound(next, all.product(all));

        Formula form = next.totalOrder(A, first, last);

        Solver solver = new Solver();
        solver.options().setSolver(SATFactory.MiniSat);
        solver.options().setBitwidth(4);
        // solver.options().setFlatten(false);
        solver.options().setIntEncoding(Options.IntEncoding.TWOSCOMPLEMENT);
        solver.options().setSymmetryBreaking(0);
        solver.options().setSkolemDepth(0);

        Iterator<Solution> sol = solver.solveAll(form, bounds);
        assertTrue(sol.hasNext());
        assertEquals(sol.next().outcome(), Solution.Outcome.TRIVIALLY_SATISFIABLE);
        assertTrue(sol.hasNext());
        assertEquals(sol.next().outcome(), Solution.Outcome.TRIVIALLY_UNSATISFIABLE);
        assertFalse(sol.hasNext());

        // int i=1;
        //
        // while (sol.hasNext()) {
        // System.out.println("================================== "+i+"
        // ===================================");
        // System.out.println(sol.next());
        // System.out.flush();
        // i++;
        // }
    }

    public final void testEmina_05072008() {
        Relation A = Relation.unary("A"), first = Relation.unary("OrdFirst"), last = Relation.unary("OrdLast"),
                        next = Relation.nary("OrdNext", 2);
        Relation B = Relation.unary("B"), acyclic = Relation.binary("acyclic");

        List<String> atomlist = Arrays.asList("A1", "A2", "A3", "B1", "B2", "B3", "C1", "C2");
        Universe universe = new Universe(atomlist);
        TupleFactory factory = universe.factory();
        Bounds bounds = new Bounds(universe);

        TupleSet allA = factory.setOf("A1", "A2", "A3");
        TupleSet allB = factory.setOf("B1", "B2", "B3");
        TupleSet allC = factory.setOf("C1", "C2");
        bounds.boundExactly(A, allA);
        bounds.bound(first, allA);
        bounds.bound(last, allA);
        bounds.bound(next, allA.product(allA));
        bounds.boundExactly(B, allB);
        bounds.bound(acyclic, allC.product(allC));

        Variable v = Variable.unary("v");
        Formula f0 = Formula.TRUE.forSome(v.setOf(B));
        Formula f1 = next.totalOrder(A, first, last);
        Formula f2 = acyclic.acyclic();
        Formula form = f0.and(f1).and(f2);

        Solver solver = new Solver();
        solver.options().setSolver(SATFactory.MiniSat);
        solver.options().setBitwidth(4);
        // solver.options().setFlatten(false);
        solver.options().setIntEncoding(Options.IntEncoding.TWOSCOMPLEMENT);
        solver.options().setSymmetryBreaking(0);
        solver.options().setSkolemDepth(0);

        Iterator<Solution> sol = solver.solveAll(form, bounds);
        int i = 1;

        while (sol.hasNext()) {
            assertTrue(i <= 17);
            sol.next();
            i++;
        }
    }

    public final void testFelix_03062008_2() {
        Relation x5 = Relation.unary("Role");
        Relation x6 = Relation.unary("Session");

        List<String> atomlist = Arrays.asList("Role$0", "Session$0", "Session$1");

        Universe universe = new Universe(atomlist);
        TupleFactory factory = universe.factory();
        Bounds bounds = new Bounds(universe);

        TupleSet x5_upper = factory.noneOf(1);
        x5_upper.add(factory.tuple("Role$0"));
        bounds.bound(x5, x5_upper);

        TupleSet x6_upper = factory.noneOf(1);
        x6_upper.add(factory.tuple("Session$0"));
        x6_upper.add(factory.tuple("Session$1"));
        bounds.bound(x6, x6_upper);

        Variable x11 = Variable.unary("x_a");
        Decls x10 = x11.oneOf(x6);
        Variable x15 = Variable.unary("x_b");
        Decls x14 = x15.oneOf(x5);
        Variable x17 = Variable.unary("x_c");
        Decls x16 = x17.oneOf(x5);
        Decls x13 = x14.and(x16);
        Expression x20 = x15.product(x17);
        Expression x19 = x11.product(x20);
        Formula x18 = x19.some();
        Formula x12 = x18.forSome(x13);
        Formula x9 = x12.forAll(x10);
        Formula x24 = x5.some();
        Formula x23 = x24.not();
        Formula x28 = x5.eq(x5);
        Formula x29 = x6.eq(x6);
        Formula x25 = x28.and(x29);
        Formula x22 = x23.and(x25);
        Formula x8 = x9.and(x22).and(x5.no()).and(x6.no());

        Solver solver = new Solver();
        solver.options().setSolver(SATFactory.DefaultSAT4J);
        solver.options().setBitwidth(2);
        // solver.options().setFlatten(false);
        solver.options().setIntEncoding(Options.IntEncoding.TWOSCOMPLEMENT);
        solver.options().setSymmetryBreaking(20);
        solver.options().setSkolemDepth(2);

        System.out.flush();

        Solution sol = solver.solve(x8, bounds);
        Instance inst = sol.instance();
        assertNotNull(inst);

        for (Relation rel : inst.relations()) {
            if (rel != x5 && rel != x6) {
                final TupleSet range = inst.tuples(x6).product(inst.tuples(x5));
                assertTrue(range.containsAll(inst.tuples(rel)));
            }
        }
    }

    public final void testFelix_03062008() {
        Relation x0 = Relation.unary("Int/min");
        Relation x1 = Relation.unary("Int/zero");
        Relation x2 = Relation.unary("Int/max");
        Relation x3 = Relation.nary("Int/next", 2);
        Relation x4 = Relation.unary("seq/Int");

        List<String> atomlist = Arrays.asList("-1", "-2", "-3", "-4", "-5", "-6", "-7", "-8", "0", "1", "2", "3", "4", "5", "6", "7");

        Universe universe = new Universe(atomlist);
        TupleFactory factory = universe.factory();
        Bounds bounds = new Bounds(universe);

        TupleSet x0_upper = factory.noneOf(1);
        x0_upper.add(factory.tuple("-8"));
        bounds.boundExactly(x0, x0_upper);

        TupleSet x1_upper = factory.noneOf(1);
        x1_upper.add(factory.tuple("0"));
        bounds.boundExactly(x1, x1_upper);

        TupleSet x2_upper = factory.noneOf(1);
        x2_upper.add(factory.tuple("7"));
        bounds.boundExactly(x2, x2_upper);

        TupleSet x3_upper = factory.noneOf(2);
        x3_upper.add(factory.tuple("-8").product(factory.tuple("-7")));
        x3_upper.add(factory.tuple("-7").product(factory.tuple("-6")));
        x3_upper.add(factory.tuple("-6").product(factory.tuple("-5")));
        x3_upper.add(factory.tuple("-5").product(factory.tuple("-4")));
        x3_upper.add(factory.tuple("-4").product(factory.tuple("-3")));
        x3_upper.add(factory.tuple("-3").product(factory.tuple("-2")));
        x3_upper.add(factory.tuple("-2").product(factory.tuple("-1")));
        x3_upper.add(factory.tuple("-1").product(factory.tuple("0")));
        x3_upper.add(factory.tuple("0").product(factory.tuple("1")));
        x3_upper.add(factory.tuple("1").product(factory.tuple("2")));
        x3_upper.add(factory.tuple("2").product(factory.tuple("3")));
        x3_upper.add(factory.tuple("3").product(factory.tuple("4")));
        x3_upper.add(factory.tuple("4").product(factory.tuple("5")));
        x3_upper.add(factory.tuple("5").product(factory.tuple("6")));
        x3_upper.add(factory.tuple("6").product(factory.tuple("7")));
        bounds.boundExactly(x3, x3_upper);

        TupleSet x4_upper = factory.noneOf(1);
        x4_upper.add(factory.tuple("0"));
        bounds.boundExactly(x4, x4_upper);

        bounds.boundExactly(-8, factory.range(factory.tuple("-8"), factory.tuple("-8")));
        bounds.boundExactly(-7, factory.range(factory.tuple("-7"), factory.tuple("-7")));
        bounds.boundExactly(-6, factory.range(factory.tuple("-6"), factory.tuple("-6")));
        bounds.boundExactly(-5, factory.range(factory.tuple("-5"), factory.tuple("-5")));
        bounds.boundExactly(-4, factory.range(factory.tuple("-4"), factory.tuple("-4")));
        bounds.boundExactly(-3, factory.range(factory.tuple("-3"), factory.tuple("-3")));
        bounds.boundExactly(-2, factory.range(factory.tuple("-2"), factory.tuple("-2")));
        bounds.boundExactly(-1, factory.range(factory.tuple("-1"), factory.tuple("-1")));
        bounds.boundExactly(0, factory.range(factory.tuple("0"), factory.tuple("0")));
        bounds.boundExactly(1, factory.range(factory.tuple("1"), factory.tuple("1")));
        bounds.boundExactly(2, factory.range(factory.tuple("2"), factory.tuple("2")));
        bounds.boundExactly(3, factory.range(factory.tuple("3"), factory.tuple("3")));
        bounds.boundExactly(4, factory.range(factory.tuple("4"), factory.tuple("4")));
        bounds.boundExactly(5, factory.range(factory.tuple("5"), factory.tuple("5")));
        bounds.boundExactly(6, factory.range(factory.tuple("6"), factory.tuple("6")));
        bounds.boundExactly(7, factory.range(factory.tuple("7"), factory.tuple("7")));

        Variable x9 = Variable.unary("x");
        Decls x8 = x9.oneOf(Expression.INTS);
        Variable x14 = Variable.unary("p_t'");
        Expression x15 = Expression.INTS.difference(x9);
        Decls x13 = x14.oneOf(x15);
        Variable x20 = Variable.unary("p_v");
        Decls x19 = x20.oneOf(Expression.INTS);
        Formula x21 = x14.in(x9);
        Expression x18 = x21.comprehension(x19);
        IntExpression x17 = x18.count();
        IntExpression x22 = IntConstant.constant(0);
        Formula x16 = x17.gt(x22);
        Formula x12 = x16.forAll(x13);
        Formula x11 = x12.not();
        Formula x7 = x11.forAll(x8);
        Formula x25 = x0.eq(x0);
        Formula x26 = x2.eq(x2);
        Formula x24 = x25.and(x26);
        Formula x27 = x3.eq(x3);
        Formula x23 = x24.and(x27);
        Formula x6 = x7.and(x23);
        Formula x29 = x1.eq(x1);
        Formula x30 = x4.eq(x4);
        Formula x28 = x29.and(x30);
        Formula x5 = x6.and(x28);

        Solver solver = new Solver();
        solver.options().setSolver(SATFactory.DefaultSAT4J);
        solver.options().setBitwidth(4);
        // solver.options().setFlatten(false);
        solver.options().setIntEncoding(Options.IntEncoding.TWOSCOMPLEMENT);
        solver.options().setSymmetryBreaking(20);

        // System.out.println(PrettyPrinter.print(x5, 2));
        solver.options().setSkolemDepth(0);
        Solution sol1 = solver.solve(x5, bounds);
        assertNotNull(sol1.instance());

        solver.options().setSkolemDepth(1);
        Solution sol2 = solver.solve(x5, bounds);
        assertNotNull(sol2.instance());
    }

    public final void testFelix_02222008() {
        List<String> atomlist = Arrays.asList("X1", "X2", "X3");

        Universe universe = new Universe(atomlist);
        TupleFactory factory = universe.factory();
        Bounds bounds = new Bounds(universe);

        Relation x = Relation.unary("X");
        TupleSet x_upper = factory.noneOf(1);
        x_upper.add(factory.tuple("X1"));
        x_upper.add(factory.tuple("X2"));
        x_upper.add(factory.tuple("X3"));
        bounds.bound(x, x_upper);

        Variable a = Variable.unary("a");
        Variable b = Variable.unary("b");
        Variable c = Variable.unary("c");
        Formula goal = x.lone().not().and(b.union(c).eq(a).forSome(c.oneOf(x)).forAll(b.oneOf(x)).forSome(a.setOf(x)));

        Solver solver = new Solver();
        solver.options().setSolver(SATFactory.DefaultSAT4J);
        solver.options().setBitwidth(4);
        solver.options().setIntEncoding(Options.IntEncoding.TWOSCOMPLEMENT);
        solver.options().setSymmetryBreaking(0);
        solver.options().setSkolemDepth(2);

        Iterator<Solution> itr = solver.solveAll(goal, bounds);
        int sols = 0;
        while (itr.hasNext()) {
            Solution sol = itr.next();
            Instance inst = sol.instance();
            if (inst == null)
                break;
            sols++;

            for (Relation rel : inst.relations()) {
                if (rel != x) {
                    if (rel.arity() == 1) { // rel = a
                        assertEquals(inst.tuples(x), inst.tuples(rel));
                    } else { // rel = c
                        final TupleSet dom = factory.noneOf(1);
                        for (Tuple t : inst.tuples(rel)) {
                            dom.add(factory.tuple(t.atom(0)));
                        }
                        assertEquals(inst.tuples(x), dom);
                    }
                }
            }
        }
        assertEquals(3, sols);
    }

    public final void testFelix_02212008() {
        Relation x0 = Relation.unary("Int/min");
        Relation x1 = Relation.unary("Int/zero");
        Relation x2 = Relation.unary("Int/max");
        Relation x3 = Relation.nary("Int/next", 2);
        Relation x4 = Relation.unary("seq/Int");

        List<String> atomlist = Arrays.asList("-1", "-2", "-3", "-4", "-5", "-6", "-7", "-8", "0", "1", "2", "3", "4", "5", "6", "7");

        Universe universe = new Universe(atomlist);
        TupleFactory factory = universe.factory();
        Bounds bounds = new Bounds(universe);

        TupleSet x0_upper = factory.noneOf(1);
        x0_upper.add(factory.tuple("-8"));
        bounds.boundExactly(x0, x0_upper);

        TupleSet x1_upper = factory.noneOf(1);
        x1_upper.add(factory.tuple("0"));
        bounds.boundExactly(x1, x1_upper);

        TupleSet x2_upper = factory.noneOf(1);
        x2_upper.add(factory.tuple("7"));
        bounds.boundExactly(x2, x2_upper);

        TupleSet x3_upper = factory.noneOf(2);
        x3_upper.add(factory.tuple("-8").product(factory.tuple("-7")));
        x3_upper.add(factory.tuple("-7").product(factory.tuple("-6")));
        x3_upper.add(factory.tuple("-6").product(factory.tuple("-5")));
        x3_upper.add(factory.tuple("-5").product(factory.tuple("-4")));
        x3_upper.add(factory.tuple("-4").product(factory.tuple("-3")));
        x3_upper.add(factory.tuple("-3").product(factory.tuple("-2")));
        x3_upper.add(factory.tuple("-2").product(factory.tuple("-1")));
        x3_upper.add(factory.tuple("-1").product(factory.tuple("0")));
        x3_upper.add(factory.tuple("0").product(factory.tuple("1")));
        x3_upper.add(factory.tuple("1").product(factory.tuple("2")));
        x3_upper.add(factory.tuple("2").product(factory.tuple("3")));
        x3_upper.add(factory.tuple("3").product(factory.tuple("4")));
        x3_upper.add(factory.tuple("4").product(factory.tuple("5")));
        x3_upper.add(factory.tuple("5").product(factory.tuple("6")));
        x3_upper.add(factory.tuple("6").product(factory.tuple("7")));
        bounds.boundExactly(x3, x3_upper);

        TupleSet x4_upper = factory.noneOf(1);
        x4_upper.add(factory.tuple("0"));
        x4_upper.add(factory.tuple("1"));
        x4_upper.add(factory.tuple("2"));
        x4_upper.add(factory.tuple("3"));
        bounds.boundExactly(x4, x4_upper);

        bounds.boundExactly(-8, factory.range(factory.tuple("-8"), factory.tuple("-8")));
        bounds.boundExactly(-7, factory.range(factory.tuple("-7"), factory.tuple("-7")));
        bounds.boundExactly(-6, factory.range(factory.tuple("-6"), factory.tuple("-6")));
        bounds.boundExactly(-5, factory.range(factory.tuple("-5"), factory.tuple("-5")));
        bounds.boundExactly(-4, factory.range(factory.tuple("-4"), factory.tuple("-4")));
        bounds.boundExactly(-3, factory.range(factory.tuple("-3"), factory.tuple("-3")));
        bounds.boundExactly(-2, factory.range(factory.tuple("-2"), factory.tuple("-2")));
        bounds.boundExactly(-1, factory.range(factory.tuple("-1"), factory.tuple("-1")));
        bounds.boundExactly(0, factory.range(factory.tuple("0"), factory.tuple("0")));
        bounds.boundExactly(1, factory.range(factory.tuple("1"), factory.tuple("1")));
        bounds.boundExactly(2, factory.range(factory.tuple("2"), factory.tuple("2")));
        bounds.boundExactly(3, factory.range(factory.tuple("3"), factory.tuple("3")));
        bounds.boundExactly(4, factory.range(factory.tuple("4"), factory.tuple("4")));
        bounds.boundExactly(5, factory.range(factory.tuple("5"), factory.tuple("5")));
        bounds.boundExactly(6, factory.range(factory.tuple("6"), factory.tuple("6")));
        bounds.boundExactly(7, factory.range(factory.tuple("7"), factory.tuple("7")));

        Variable x9 = Variable.nary("isTree_r", 2);
        Expression x10 = Expression.INTS.product(Expression.INTS);
        Decls x8 = x9.setOf(x10);
        Expression x15 = Expression.INTS.product(Expression.INTS);
        Formula x14 = x9.in(x15);
        Formula x13 = x14.and(Formula.TRUE);
        Formula x12 = x13.and(Formula.TRUE);
        Formula x7 = x12.forSome(x8);
        Formula x19 = x0.eq(x0);
        Formula x20 = x2.eq(x2);
        Formula x18 = x19.and(x20);
        Formula x21 = x3.eq(x3);
        Formula x17 = x18.and(x21);
        Formula x6 = x7.and(x17);
        Formula x23 = x1.eq(x1);
        Formula x24 = x4.eq(x4);
        Formula x22 = x23.and(x24);
        Formula x5 = x6.and(x22);

        Solver solver = new Solver();
        solver.options().setSolver(SATFactory.DefaultSAT4J);
        solver.options().setBitwidth(4);
        solver.options().setIntEncoding(Options.IntEncoding.TWOSCOMPLEMENT);
        solver.options().setSymmetryBreaking(20);
        solver.options().setSkolemDepth(0);

        Iterator<Solution> sols = solver.solveAll(x5, bounds);
        assertTrue(sols.hasNext());
        Solution a = sols.next();
        assertEquals(Solution.Outcome.TRIVIALLY_SATISFIABLE, a.outcome());
        assertTrue(sols.hasNext());
        a = sols.next();
        assertEquals(Solution.Outcome.SATISFIABLE, a.outcome());

    }

    public final void testFelix_11262007() {
        Relation x6 = Relation.unary("R2");

        List<String> atomlist = Arrays.asList("X", "Y", "Z");
        Universe universe = new Universe(atomlist);
        TupleFactory factory = universe.factory();
        Bounds bounds = new Bounds(universe);

        bounds.bound(x6, factory.allOf(1));

        final Variable x32 = Variable.unary("a");
        final Decls x31 = x32.oneOf(x6);

        final Variable x36 = Variable.unary("b");
        final Decls x35 = x36.oneOf(x32.join(x6.product(x6)));

        final Formula x29 = x36.some().forSome(x35).forSome(x31);

        Solver solver = new Solver();

        solver.options().setSolver(SATFactory.DefaultSAT4J);
        solver.options().setBitwidth(4);
        solver.options().setIntEncoding(Options.IntEncoding.TWOSCOMPLEMENT);
        solver.options().setSymmetryBreaking(20);
        solver.options().setSkolemDepth(0);
        final Set<Decl> decls = new LinkedHashSet<Decl>();
        solver.options().setReporter(new AbstractReporter() {

            @Override
            public void skolemizing(Decl decl, Relation skolem, List<Decl> predecl) {
                decls.add(decl);
            }
        });

        Solution sol = solver.solve(x29, bounds);
        assertEquals(2, decls.size());
        assertTrue(decls.contains(x31));
        assertTrue(decls.contains(x35));
        assertNotNull(sol.instance());

    }

    public final void testFelix_11192007() {
        List<String> atomlist = Arrays.asList("A", "B", "C");

        Universe universe = new Universe(atomlist);

        Bounds bounds = new Bounds(universe);

        Solver solver = new Solver();

        solver.options().setLogTranslation(2);
        solver.options().setSolver(SATFactory.MiniSatProver);
        solver.options().setBitwidth(4);
        solver.options().setIntEncoding(Options.IntEncoding.TWOSCOMPLEMENT);
        solver.options().setSymmetryBreaking(20);
        solver.options().setSkolemDepth(0);

        Solution sol = solver.solve(Formula.TRUE, bounds);
        assertNotNull(sol.instance());
    }

    private static boolean isMinimal(Solver solver, Bounds bounds, Set<Formula> core) {
        final Set<Formula> minCore = new LinkedHashSet<Formula>(core);
        for (Iterator<Formula> itr = minCore.iterator(); itr.hasNext();) {
            Formula f = itr.next();
            Formula noF = Formula.TRUE;
            for (Formula f1 : minCore) {
                if (f != f1)
                    noF = noF.and(f1);
            }
            if (solver.solve(noF, bounds).instance() == null) {
                itr.remove();
            }
        }
        if (minCore.size() == core.size()) {
            return true;
        } else {
            System.out.println("minimal core is: ");
            for (Formula f : minCore) {
                System.out.println(f);
            }
            System.out.println("found core is: ");
            for (Formula f : core) {
                System.out.println(f);
            }
            return false;
        }
    }

    public final void testFelix_05192007() {
        Relation x5 = Relation.nary("this/de", 1);
        Relation x6 = Relation.nary("this/dir", 1);
        Relation x7 = Relation.nary("this/de.contents", 2);
        Relation x8 = Relation.nary("this/dir.entries", 2);
        Relation x9 = Relation.nary("this/dir.parent", 2);

        List<String> atomlist = Arrays.asList("de[0]", "de[1]", "de[2]", "de[3]", "dir[0]", "dir[1]", "dir[2]", "dir[3]");

        Universe universe = new Universe(atomlist);
        TupleFactory factory = universe.factory();
        Bounds bounds = new Bounds(universe);

        TupleSet x5_upper = factory.noneOf(1);
        x5_upper.add(factory.tuple("de[0]"));
        x5_upper.add(factory.tuple("de[1]"));
        x5_upper.add(factory.tuple("de[2]"));
        x5_upper.add(factory.tuple("de[3]"));
        bounds.bound(x5, x5_upper);

        TupleSet x6_upper = factory.noneOf(1);
        x6_upper.add(factory.tuple("dir[0]"));
        x6_upper.add(factory.tuple("dir[1]"));
        x6_upper.add(factory.tuple("dir[2]"));
        x6_upper.add(factory.tuple("dir[3]"));
        bounds.bound(x6, x6_upper);

        TupleSet x7_upper = factory.noneOf(2);
        x7_upper.add(factory.tuple("de[0]").product(factory.tuple("dir[0]")));
        x7_upper.add(factory.tuple("de[0]").product(factory.tuple("dir[1]")));
        x7_upper.add(factory.tuple("de[0]").product(factory.tuple("dir[2]")));
        x7_upper.add(factory.tuple("de[0]").product(factory.tuple("dir[3]")));
        x7_upper.add(factory.tuple("de[1]").product(factory.tuple("dir[0]")));
        x7_upper.add(factory.tuple("de[1]").product(factory.tuple("dir[1]")));
        x7_upper.add(factory.tuple("de[1]").product(factory.tuple("dir[2]")));
        x7_upper.add(factory.tuple("de[1]").product(factory.tuple("dir[3]")));
        x7_upper.add(factory.tuple("de[2]").product(factory.tuple("dir[0]")));
        x7_upper.add(factory.tuple("de[2]").product(factory.tuple("dir[1]")));
        x7_upper.add(factory.tuple("de[2]").product(factory.tuple("dir[2]")));
        x7_upper.add(factory.tuple("de[2]").product(factory.tuple("dir[3]")));
        x7_upper.add(factory.tuple("de[3]").product(factory.tuple("dir[0]")));
        x7_upper.add(factory.tuple("de[3]").product(factory.tuple("dir[1]")));
        x7_upper.add(factory.tuple("de[3]").product(factory.tuple("dir[2]")));
        x7_upper.add(factory.tuple("de[3]").product(factory.tuple("dir[3]")));
        bounds.bound(x7, x7_upper);

        TupleSet x8_upper = factory.noneOf(2);
        x8_upper.add(factory.tuple("dir[0]").product(factory.tuple("de[0]")));
        x8_upper.add(factory.tuple("dir[0]").product(factory.tuple("de[1]")));
        x8_upper.add(factory.tuple("dir[0]").product(factory.tuple("de[2]")));
        x8_upper.add(factory.tuple("dir[0]").product(factory.tuple("de[3]")));
        x8_upper.add(factory.tuple("dir[1]").product(factory.tuple("de[0]")));
        x8_upper.add(factory.tuple("dir[1]").product(factory.tuple("de[1]")));
        x8_upper.add(factory.tuple("dir[1]").product(factory.tuple("de[2]")));
        x8_upper.add(factory.tuple("dir[1]").product(factory.tuple("de[3]")));
        x8_upper.add(factory.tuple("dir[2]").product(factory.tuple("de[0]")));
        x8_upper.add(factory.tuple("dir[2]").product(factory.tuple("de[1]")));
        x8_upper.add(factory.tuple("dir[2]").product(factory.tuple("de[2]")));
        x8_upper.add(factory.tuple("dir[2]").product(factory.tuple("de[3]")));
        x8_upper.add(factory.tuple("dir[3]").product(factory.tuple("de[0]")));
        x8_upper.add(factory.tuple("dir[3]").product(factory.tuple("de[1]")));
        x8_upper.add(factory.tuple("dir[3]").product(factory.tuple("de[2]")));
        x8_upper.add(factory.tuple("dir[3]").product(factory.tuple("de[3]")));
        bounds.bound(x8, x8_upper);

        TupleSet x9_upper = factory.noneOf(2);
        x9_upper.add(factory.tuple("dir[0]").product(factory.tuple("dir[0]")));
        x9_upper.add(factory.tuple("dir[0]").product(factory.tuple("dir[1]")));
        x9_upper.add(factory.tuple("dir[0]").product(factory.tuple("dir[2]")));
        x9_upper.add(factory.tuple("dir[0]").product(factory.tuple("dir[3]")));
        x9_upper.add(factory.tuple("dir[1]").product(factory.tuple("dir[0]")));
        x9_upper.add(factory.tuple("dir[1]").product(factory.tuple("dir[1]")));
        x9_upper.add(factory.tuple("dir[1]").product(factory.tuple("dir[2]")));
        x9_upper.add(factory.tuple("dir[1]").product(factory.tuple("dir[3]")));
        x9_upper.add(factory.tuple("dir[2]").product(factory.tuple("dir[0]")));
        x9_upper.add(factory.tuple("dir[2]").product(factory.tuple("dir[1]")));
        x9_upper.add(factory.tuple("dir[2]").product(factory.tuple("dir[2]")));
        x9_upper.add(factory.tuple("dir[2]").product(factory.tuple("dir[3]")));
        x9_upper.add(factory.tuple("dir[3]").product(factory.tuple("dir[0]")));
        x9_upper.add(factory.tuple("dir[3]").product(factory.tuple("dir[1]")));
        x9_upper.add(factory.tuple("dir[3]").product(factory.tuple("dir[2]")));
        x9_upper.add(factory.tuple("dir[3]").product(factory.tuple("dir[3]")));
        bounds.bound(x9, x9_upper);

        Expression x39 = x5.union(Expression.INTS);
        Expression x38 = x6.union(x39);
        Expression x37 = x38.product(Expression.UNIV);
        Expression x35 = Expression.IDEN.intersection(x37);
        Expression x34 = x35.intersection(x7);
        Formula x33 = x34.no();
        Variable x44 = Variable.nary("functional_x", 1);
        Decls x43 = x44.oneOf(x5);
        Expression x48 = x44.join(x7);
        Formula x47 = x48.lone();
        Formula x45 = Formula.TRUE.implies(x47);
        Formula x42 = x45.forAll(x43);
        Formula x32 = x33.and(x42);
        Variable x51 = Variable.nary("total_x", 1);
        Decls x50 = x51.oneOf(x5);
        Expression x54 = x51.join(x7);
        Formula x53 = x54.some();
        Formula x52 = Formula.TRUE.implies(x53);
        Formula x49 = x52.forAll(x50);
        Formula x31 = x32.and(x49);
        Variable x57 = Variable.nary("injective_x", 1);
        Decls x56 = x57.oneOf(x6);
        Expression x60 = x7.join(x57);
        Formula x59 = x60.lone();
        Formula x58 = Formula.TRUE.implies(x59);
        Formula x55 = x58.forAll(x56);
        Formula x30 = x31.and(x55);
        Expression x63 = x7.join(x8);
        Expression x62 = x63.transpose();
        Formula x61 = x62.in(x63);
        Formula x29 = x30.and(x61);
        Variable x66 = Variable.nary("acyclic_x", 1);
        Decls x65 = x66.oneOf(x5);
        Expression x72 = x7.join(x8);
        Expression x71 = x72.closure();
        Expression x70 = x66.join(x71);
        Formula x69 = x66.in(x70);
        Formula x68 = x69.not();
        Formula x67 = Formula.TRUE.implies(x68);
        Formula x64 = x67.forAll(x65);
        Formula x28 = x29.and(x64);
        Variable x75 = Variable.nary("surjective_x", 1);
        Decls x74 = x75.oneOf(x5);
        Expression x78 = x8.join(x75);
        Formula x77 = x78.some();
        Formula x76 = Formula.TRUE.implies(x77);
        Formula x73 = x76.forAll(x74);
        Formula x27 = x28.and(x73);
        Variable x81 = Variable.nary("functional_x", 1);
        Decls x80 = x81.oneOf(x6);
        Expression x84 = x81.join(x8);
        Formula x83 = x84.lone();
        Formula x82 = Formula.TRUE.implies(x83);
        Formula x79 = x82.forAll(x80);
        Formula x26 = x27.and(x79);
        Variable x87 = Variable.nary("acyclic_x", 1);
        Decls x86 = x87.oneOf(x6);
        Expression x93 = x8.join(x7);
        Expression x92 = x93.closure();
        Expression x91 = x87.join(x92);
        Formula x90 = x87.in(x91);
        Formula x89 = x90.not();
        Formula x88 = Formula.TRUE.implies(x89);
        Formula x85 = x88.forAll(x86);
        Formula x25 = x26.and(x85);
        Expression x96 = x9.transpose();
        Expression x95 = x96.intersection(x9);
        Expression x98 = x38.product(Expression.UNIV);
        Expression x97 = Expression.IDEN.intersection(x98);
        Formula x94 = x95.in(x97);
        Formula x24 = x25.and(x94);
        Expression x102 = x38.product(Expression.UNIV);
        Expression x101 = Expression.IDEN.intersection(x102);
        Expression x100 = x101.intersection(x9);
        Formula x99 = x100.no();
        Formula x23 = x24.and(x99);
        Expression x106 = x38.product(Expression.UNIV);
        Expression x105 = Expression.IDEN.intersection(x106);
        Expression x104 = x105.intersection(x8);
        Formula x103 = x104.no();
        Formula x22 = x23.and(x103);
        Variable x109 = Variable.nary("injective_x", 1);
        Decls x108 = x109.oneOf(x5);
        Expression x112 = x8.join(x109);
        Formula x111 = x112.lone();
        Formula x110 = Formula.TRUE.implies(x111);
        Formula x107 = x110.forAll(x108);
        Formula x21 = x22.and(x107);
        Variable x115 = Variable.nary("acyclic_x", 1);
        Decls x114 = x115.oneOf(x6);
        Expression x120 = x9.closure();
        Expression x119 = x115.join(x120);
        Formula x118 = x115.in(x119);
        Formula x117 = x118.not();
        Formula x116 = Formula.TRUE.implies(x117);
        Formula x113 = x116.forAll(x114);
        Formula x20 = x21.and(x113);
        Variable x123 = Variable.nary("functional_x", 1);
        Decls x122 = x123.oneOf(x6);
        Expression x126 = x123.join(x9);
        Formula x125 = x126.lone();
        Formula x124 = Formula.TRUE.implies(x125);
        Formula x121 = x124.forAll(x122);
        Formula x19 = x20.and(x121);
        Variable x129 = Variable.nary("injective_x", 1);
        Decls x128 = x129.oneOf(x6);
        Expression x132 = x9.join(x129);
        Formula x131 = x132.lone();
        Formula x130 = Formula.TRUE.implies(x131);
        Formula x127 = x130.forAll(x128);
        Formula x18 = x19.and(x127);
        Variable x137 = Variable.nary("rootedOne_root", 1);
        Decls x136 = x137.oneOf(x6);
        Variable x139 = Variable.nary("rootedOne_root", 1);
        Decls x138 = x139.oneOf(x6);
        Decls x135 = x136.and(x138);
        Expression x146 = x9.closure();
        Expression x148 = x38.product(Expression.UNIV);
        Expression x147 = Expression.IDEN.intersection(x148);
        Expression x145 = x146.union(x147);
        Expression x144 = x137.join(x145);
        Formula x143 = x6.in(x144);
        Expression x152 = x9.closure();
        Expression x154 = x38.product(Expression.UNIV);
        Expression x153 = Expression.IDEN.intersection(x154);
        Expression x151 = x152.union(x153);
        Expression x150 = x139.join(x151);
        Formula x149 = x6.in(x150);
        Formula x142 = x143.and(x149);
        Formula x156 = x137.eq(x139);
        Formula x155 = x156.and(Formula.TRUE);
        Formula x141 = x142.implies(x155);
        Formula x140 = Formula.TRUE.implies(x141);
        Formula x134 = x140.forAll(x135);
        Variable x159 = Variable.nary("rootedOne_root", 1);
        Decls x158 = x159.oneOf(x6);
        Expression x164 = x9.closure();
        Expression x166 = x38.product(Expression.UNIV);
        Expression x165 = Expression.IDEN.intersection(x166);
        Expression x163 = x164.union(x165);
        Expression x162 = x159.join(x163);
        Formula x161 = x6.in(x162);
        Formula x160 = Formula.TRUE.and(x161);
        Formula x157 = x160.forSome(x158);
        Formula x133 = x134.and(x157);
        Formula x17 = x18.and(x133);
        Variable x170 = Variable.nary("weaklyConnected_d", 1);
        Decls x169 = x170.oneOf(x6);
        Variable x172 = Variable.nary("weaklyConnected_g", 1);
        Decls x171 = x172.oneOf(x6);
        Decls x168 = x169.and(x171);
        Formula x177 = x170.eq(x172);
        Formula x176 = x177.not();
        Formula x175 = x176.not();
        Expression x182 = x9.transpose();
        Expression x181 = x9.union(x182);
        Expression x180 = x181.closure();
        Expression x179 = x172.join(x180);
        Formula x178 = x170.in(x179);
        Formula x174 = x175.or(x178);
        Formula x173 = Formula.TRUE.implies(x174);
        Formula x167 = x173.forAll(x168);
        Formula x16 = x17.and(x167);
        Expression x187 = x8.join(x7);
        Expression x188 = Expression.UNIV.product(x6);
        Expression x186 = x187.intersection(x188);
        Expression x185 = x9.union(x186);
        Expression x184 = x185.transpose();
        Formula x183 = x184.in(x185);
        Formula x15 = x16.and(x183);
        Variable x191 = Variable.nary("inner_injective_x", 1);
        Variable x197 = Variable.nary("ternary_a", 1);
        Expression x198 = x7.join(x38);
        Decls x196 = x197.oneOf(x198);
        Variable x200 = Variable.nary("ternary_b", 1);
        Expression x202 = x38.join(x7);
        Expression x203 = x8.join(x38);
        Expression x201 = x202.intersection(x203);
        Decls x199 = x200.oneOf(x201);
        Variable x205 = Variable.nary("ternary_c", 1);
        Expression x206 = x38.join(x8);
        Decls x204 = x205.oneOf(x206);
        Decls x195 = x196.and(x199).and(x204);
        Expression x209 = x197.product(x200);
        Formula x208 = x209.in(x7);
        Expression x211 = x200.product(x205);
        Formula x210 = x211.in(x8);
        Formula x207 = x208.and(x210);
        Expression x194 = x207.comprehension(x195);
        Expression x193 = x194.join(x38);
        Expression x192 = x193.join(x38);
        Decls x190 = x191.oneOf(x192);
        Variable x215 = Variable.nary("injective_x", 1);
        Expression x217 = x191.join(x194);
        Expression x216 = x38.join(x217);
        Decls x214 = x215.oneOf(x216);
        Expression x221 = x191.join(x194);
        Expression x220 = x221.join(x215);
        Formula x219 = x220.lone();
        Formula x218 = Formula.TRUE.implies(x219);
        Formula x213 = x218.forAll(x214);
        Formula x212 = Formula.TRUE.implies(x213);
        Formula x189 = x212.forAll(x190);
        Formula x14 = x15.and(x189);
        Variable x224 = Variable.nary("inner_injective_x", 1);
        Variable x230 = Variable.nary("ternary_a", 1);
        Expression x231 = x8.join(x38);
        Decls x229 = x230.oneOf(x231);
        Variable x233 = Variable.nary("ternary_b", 1);
        Expression x235 = x38.join(x8);
        Expression x236 = x7.join(x38);
        Expression x234 = x235.intersection(x236);
        Decls x232 = x233.oneOf(x234);
        Variable x238 = Variable.nary("ternary_c", 1);
        Expression x239 = x38.join(x7);
        Decls x237 = x238.oneOf(x239);
        Decls x228 = x229.and(x232).and(x237);
        Expression x242 = x230.product(x233);
        Formula x241 = x242.in(x8);
        Expression x244 = x233.product(x238);
        Formula x243 = x244.in(x7);
        Formula x240 = x241.and(x243);
        Expression x227 = x240.comprehension(x228);
        Expression x226 = x227.join(x38);
        Expression x225 = x226.join(x38);
        Decls x223 = x224.oneOf(x225);
        Variable x248 = Variable.nary("injective_x", 1);
        Expression x250 = x224.join(x227);
        Expression x249 = x38.join(x250);
        Decls x247 = x248.oneOf(x249);
        Expression x254 = x224.join(x227);
        Expression x253 = x254.join(x248);
        Formula x252 = x253.lone();
        Formula x251 = Formula.TRUE.implies(x252);
        Formula x246 = x251.forAll(x247);
        Formula x245 = Formula.TRUE.implies(x246);
        Formula x222 = x245.forAll(x223);
        Formula x13 = x14.and(x222);
        Variable x259 = Variable.nary("rootedOne_root", 1);
        Decls x258 = x259.oneOf(x6);
        Variable x261 = Variable.nary("rootedOne_root", 1);
        Decls x260 = x261.oneOf(x6);
        Decls x257 = x258.and(x260);
        Variable x272 = Variable.nary("rootedOne_a", 1);
        Decls x271 = x272.oneOf(x6);
        Variable x274 = Variable.nary("rootedOne_b", 1);
        Decls x273 = x274.oneOf(x6);
        Decls x270 = x271.and(x273);
        Variable x277 = Variable.nary("rootedOne_c", 1);
        Decls x276 = x277.oneOf(x38);
        Expression x281 = x277.product(x274);
        Expression x280 = x272.product(x281);
        Variable x285 = Variable.nary("ternary_a", 1);
        Expression x286 = x8.join(x38);
        Decls x284 = x285.oneOf(x286);
        Variable x288 = Variable.nary("ternary_b", 1);
        Expression x290 = x38.join(x8);
        Expression x291 = x7.join(x38);
        Expression x289 = x290.intersection(x291);
        Decls x287 = x288.oneOf(x289);
        Variable x293 = Variable.nary("ternary_c", 1);
        Expression x294 = x38.join(x7);
        Decls x292 = x293.oneOf(x294);
        Decls x283 = x284.and(x287).and(x292);
        Expression x297 = x285.product(x288);
        Formula x296 = x297.in(x8);
        Expression x299 = x288.product(x293);
        Formula x298 = x299.in(x7);
        Formula x295 = x296.and(x298);
        Expression x282 = x295.comprehension(x283);
        Formula x279 = x280.in(x282);
        Formula x278 = Formula.TRUE.and(x279);
        Formula x275 = x278.forSome(x276);
        Expression x269 = x275.comprehension(x270);
        Expression x268 = x269.closure();
        Expression x301 = x38.product(Expression.UNIV);
        Expression x300 = Expression.IDEN.intersection(x301);
        Expression x267 = x268.union(x300);
        Expression x266 = x259.join(x267);
        Formula x265 = x6.in(x266);
        Variable x309 = Variable.nary("rootedOne_a", 1);
        Decls x308 = x309.oneOf(x6);
        Variable x311 = Variable.nary("rootedOne_b", 1);
        Decls x310 = x311.oneOf(x6);
        Decls x307 = x308.and(x310);
        Variable x314 = Variable.nary("rootedOne_c", 1);
        Decls x313 = x314.oneOf(x38);
        Expression x318 = x314.product(x311);
        Expression x317 = x309.product(x318);
        Formula x316 = x317.in(x282);
        Formula x315 = Formula.TRUE.and(x316);
        Formula x312 = x315.forSome(x313);
        Expression x306 = x312.comprehension(x307);
        Expression x305 = x306.closure();
        Expression x320 = x38.product(Expression.UNIV);
        Expression x319 = Expression.IDEN.intersection(x320);
        Expression x304 = x305.union(x319);
        Expression x303 = x261.join(x304);
        Formula x302 = x6.in(x303);
        Formula x264 = x265.and(x302);
        Formula x322 = x259.eq(x261);
        Formula x321 = x322.and(Formula.TRUE);
        Formula x263 = x264.implies(x321);
        Formula x262 = Formula.TRUE.implies(x263);
        Formula x256 = x262.forAll(x257);
        Variable x325 = Variable.nary("rootedOne_root", 1);
        Decls x324 = x325.oneOf(x6);
        Variable x334 = Variable.nary("rootedOne_a", 1);
        Decls x333 = x334.oneOf(x6);
        Variable x336 = Variable.nary("rootedOne_b", 1);
        Decls x335 = x336.oneOf(x6);
        Decls x332 = x333.and(x335);
        Variable x339 = Variable.nary("rootedOne_c", 1);
        Decls x338 = x339.oneOf(x38);
        Expression x343 = x339.product(x336);
        Expression x342 = x334.product(x343);
        Formula x341 = x342.in(x282);
        Formula x340 = Formula.TRUE.and(x341);
        Formula x337 = x340.forSome(x338);
        Expression x331 = x337.comprehension(x332);
        Expression x330 = x331.closure();
        Expression x345 = x38.product(Expression.UNIV);
        Expression x344 = Expression.IDEN.intersection(x345);
        Expression x329 = x330.union(x344);
        Expression x328 = x325.join(x329);
        Formula x327 = x6.in(x328);
        Formula x326 = Formula.TRUE.and(x327);
        Formula x323 = x326.forSome(x324);
        Formula x255 = x256.and(x323);
        Formula x12 = x13.and(x255);
        Expression x348 = x9.join(x9);
        Formula x347 = x348.in(x9);
        Formula x346 = x347.not();
        Formula x11 = x12.and(x346);
        Expression x352 = x6.product(x6);
        Formula x351 = x9.in(x352);
        Expression x355 = x6.product(x5);
        Formula x354 = x8.in(x355);
        Expression x359 = x5.product(x6);
        Formula x358 = x7.in(x359);
        Formula x363 = Formula.TRUE.and(Formula.TRUE);
        Formula x362 = Formula.TRUE.and(x363);
        Formula x361 = Formula.TRUE.and(x362);
        Formula x360 = Formula.TRUE.and(x361);
        Formula x357 = x358.and(x360);
        Formula x356 = Formula.TRUE.and(x357);
        Formula x353 = x354.and(x356);
        Formula x350 = x351.and(x353);
        Formula x349 = Formula.TRUE.and(x350);
        Formula x10 = x11.and(x349);

        Solver solver = new Solver();
        solver.options().setLogTranslation(1);
        solver.options().setSolver(SATFactory.MiniSatProver);
        solver.options().setBitwidth(4);
        solver.options().setIntEncoding(Options.IntEncoding.TWOSCOMPLEMENT);
        Solution sol = solver.solve(x10, bounds);
        // System.out.println(sol.toString());
        Proof proof = sol.proof();
        proof.minimize(new RCEStrategy(proof.log()));
        Set<Formula> core = Nodes.minRoots(x10, sol.proof().highLevelCore().values());

        // final Set<Formula> minCore = new LinkedHashSet<Formula>(core);
        // for(Iterator<Formula> itr = minCore.iterator(); itr.hasNext();) {
        // Formula f = itr.next();
        // Formula noF = Formula.TRUE;
        // for( Formula f1 : minCore ) {
        // if (f!=f1)
        // noF = noF.and(f1);
        // }
        // if (solver.solve(noF, bounds).instance()==null) {
        // itr.remove();
        // }
        // }
        // assertTrue(minCore.size()==core.size());
        assertTrue(isMinimal(solver, bounds, core));
    }

    public final void testFelix_05152007_3() {
        Relation x5 = Relation.nary("A", 1);

        List<String> atomlist = Arrays.asList("A[0]", "A[1]", "A[2]");

        Universe universe = new Universe(atomlist);
        TupleFactory factory = universe.factory();
        Bounds bounds = new Bounds(universe);

        TupleSet x5_upper = factory.noneOf(1);
        x5_upper.add(factory.tuple("A[0]"));
        x5_upper.add(factory.tuple("A[1]"));
        x5_upper.add(factory.tuple("A[2]"));

        bounds.bound(x5, x5_upper);

        Formula a = x5.some();
        Formula a1 = x5.no();
        Formula b = a1.and(Formula.TRUE.and(Formula.TRUE));
        Formula c = a.and(b);

        Solver solver = new Solver();

        solver.options().setLogTranslation(1);
        solver.options().setSolver(SATFactory.DefaultSAT4J);
        solver.options().setBitwidth(4);
        solver.options().setIntEncoding(Options.IntEncoding.TWOSCOMPLEMENT);

        Solution sol = solver.solve(c, bounds);
        Set<Formula> core = Nodes.minRoots(c, sol.proof().highLevelCore().values());

        assertEquals(2, core.size());
        assertTrue(core.contains(a));
        assertTrue(core.contains(a1));

    }

    public final void testFelix_05152007_2() {
        Relation x5 = Relation.nary("A", 1);

        List<String> atomlist = Arrays.asList("A0", "A1", "A2");

        Universe universe = new Universe(atomlist);
        TupleFactory factory = universe.factory();

        Bounds bounds = new Bounds(universe);

        TupleSet x5_upper = factory.noneOf(1);
        x5_upper.add(factory.tuple("A2"));
        x5_upper.add(factory.tuple("A1"));
        x5_upper.add(factory.tuple("A0"));

        bounds.bound(x5, x5_upper);

        Formula x7 = x5.eq(x5).not();

        Solver solver = new Solver();

        solver.options().setLogTranslation(1);
        solver.options().setSolver(SATFactory.MiniSatProver);
        solver.options().setBitwidth(4);
        solver.options().setIntEncoding(Options.IntEncoding.TWOSCOMPLEMENT);

        Solution sol = solver.solve(x7, bounds);
        Set<Formula> core = Nodes.minRoots(x7, sol.proof().highLevelCore().values());
        assertEquals(1, core.size());
        assertTrue(core.contains(x7));
    }

    public final void testFelix_05152007_1() {
        Relation x5 = Relation.nary("A", 1);

        List<String> atomlist = Arrays.asList("A0", "A1", "A2");

        Universe universe = new Universe(atomlist);
        TupleFactory factory = universe.factory();
        Bounds bounds = new Bounds(universe);

        TupleSet x5_upper = factory.noneOf(1);
        x5_upper.add(factory.tuple("A2"));
        x5_upper.add(factory.tuple("A1"));
        x5_upper.add(factory.tuple("A0"));

        bounds.bound(x5, x5_upper);

        Formula x7 = x5.some();
        Formula x8 = x5.no();

        Formula x6 = x7.and(x8);

        Solver solver = new Solver();
        solver.options().setLogTranslation(1);

        solver.options().setSolver(SATFactory.MiniSatProver);
        solver.options().setBitwidth(4);
        solver.options().setIntEncoding(Options.IntEncoding.TWOSCOMPLEMENT);

        Solution sol = solver.solve(x6, bounds);

        // System.out.println("Sol="+sol);

        Set<Formula> core = Nodes.minRoots(x6, sol.proof().highLevelCore().values());
        assertEquals(2, core.size());
        assertTrue(core.contains(x7));
        assertTrue(core.contains(x8));

    }

    public final void testMana_01312007() {
        final Relation A = Relation.unary("A");
        final Relation first1 = Relation.unary("first1");
        final Relation first2 = Relation.unary("first2");
        final Relation last1 = Relation.unary("last1");
        final Relation last2 = Relation.unary("last2");
        final Relation next1 = Relation.binary("next1");
        final Relation next2 = Relation.binary("next2");

        final Formula f0 = next1.totalOrder(A, first1, last1);
        final Formula f1 = next2.totalOrder(A, first2, last2);
        final Formula f2 = first1.eq(last2);

        final Formula f3 = f0.and(f1).and(f2);

        final Universe u = new Universe(Arrays.asList("a0", "a1", "a2"));
        final TupleFactory f = u.factory();
        final Bounds b = new Bounds(u);

        b.bound(A, f.allOf(1));
        b.bound(first1, f.allOf(1));
        b.bound(first2, f.allOf(1));
        b.bound(last1, f.allOf(1));
        b.bound(last2, f.allOf(1));
        b.bound(next1, f.allOf(2));
        b.bound(next2, f.allOf(2));

        final Solver solver = new Solver();
        final Solution sol = solver.solve(f3, b);

        assertEquals(Solution.Outcome.SATISFIABLE, sol.outcome());
    }

    public final void testFelix_01132007() {
        // Relation x1 = Relation.nary("A",1);
        // List<String> atomlist = Arrays.asList("A0", "A1", "A2");
        //
        // Universe universe = new Universe(atomlist);
        // TupleFactory factory = universe.factory();
        // Bounds bounds = new Bounds(universe);
        //
        // TupleSet x1_upper = factory.noneOf(1);
        //
        // x1_upper.add(factory.tuple("A0"));
        // x1_upper.add(factory.tuple("A1"));
        // x1_upper.add(factory.tuple("A2"));
        //
        // bounds.bound(x1, x1_upper);
        // Solver solver = new Solver();
        //
        // solver.options().setSolver(SATFactory.MiniSat);
        // solver.options().setSymmetryBreaking(0);
        // Iterator<Solution> sols = solver.solveAll(Formula.TRUE, bounds);
        // int i = 0;
        // while (sols.hasNext() && i < 9) {
        // System.out.println("Solution"+i+": " + sols.next().instance());
        // i++;
        // }

    }

    public final void testFelix_01062007() {
        Relation x1 = Relation.nary("A", 1);
        List<String> atomlist = Arrays.asList("A");
        Universe universe = new Universe(atomlist);
        TupleFactory factory = universe.factory();
        Bounds bounds = new Bounds(universe);

        TupleSet x1_upper = factory.noneOf(1);
        x1_upper.add(factory.tuple("A"));
        bounds.bound(x1, x1_upper);

        Solver solver = new Solver();
        solver.options().setSolver(SATFactory.MiniSat);

        Iterator<Solution> sols = solver.solveAll(Formula.TRUE, bounds);
        assertNotNull(sols.next().instance());

        assertNotNull(sols.next().instance());

        assertNull(sols.next().instance());

        // Solution sol1=sols.next();
        // System.out.println("Solution1:"+sol1.instance());
        //
        // Solution sol2=sols.next();
        // System.out.println("Solution2:"+sol2.instance());
        //
        // Solution sol3=sols.next();
        // System.out.println("Solution3:"+sol3.instance());

    }

    public final void testFelix_01032007() {
        List<String> atomlist = Arrays.asList("-1", "-2", "-3", "-4", "-5", "-6", "-7", "-8", "0", "1", "2", "3", "4", "5", "6", "7");

        Universe universe = new Universe(atomlist);
        TupleFactory factory = universe.factory();
        Bounds bounds = new Bounds(universe);

        bounds.boundExactly(-8, factory.range(factory.tuple("-8"), factory.tuple("-8")));
        bounds.boundExactly(-7, factory.range(factory.tuple("-7"), factory.tuple("-7")));
        bounds.boundExactly(-6, factory.range(factory.tuple("-6"), factory.tuple("-6")));
        bounds.boundExactly(-5, factory.range(factory.tuple("-5"), factory.tuple("-5")));
        bounds.boundExactly(-4, factory.range(factory.tuple("-4"), factory.tuple("-4")));
        bounds.boundExactly(-3, factory.range(factory.tuple("-3"), factory.tuple("-3")));
        bounds.boundExactly(-2, factory.range(factory.tuple("-2"), factory.tuple("-2")));
        bounds.boundExactly(-1, factory.range(factory.tuple("-1"), factory.tuple("-1")));
        bounds.boundExactly(0, factory.range(factory.tuple("0"), factory.tuple("0")));
        bounds.boundExactly(1, factory.range(factory.tuple("1"), factory.tuple("1")));
        bounds.boundExactly(2, factory.range(factory.tuple("2"), factory.tuple("2")));
        bounds.boundExactly(3, factory.range(factory.tuple("3"), factory.tuple("3")));
        bounds.boundExactly(4, factory.range(factory.tuple("4"), factory.tuple("4")));
        bounds.boundExactly(5, factory.range(factory.tuple("5"), factory.tuple("5")));
        bounds.boundExactly(6, factory.range(factory.tuple("6"), factory.tuple("6")));
        bounds.boundExactly(7, factory.range(factory.tuple("7"), factory.tuple("7")));

        Expression set = IntConstant.constant(8).toExpression();

        Solver solver = new Solver();
        solver.options().setSolver(SATFactory.DefaultSAT4J);
        solver.options().setBitwidth(4);
        solver.options().setIntEncoding(Options.IntEncoding.TWOSCOMPLEMENT);
        Solution sol = solver.solve(set.some(), bounds);

        assertNotNull("expected SATISFIABLE but was " + sol.outcome(), sol.instance());

        Evaluator eval = new Evaluator(sol.instance(), solver.options());
        TupleSet ts = eval.evaluate(set);
        assertFalse(ts.size() == 0);

    }

    public final void testFelix_11122006() {
        Relation x0 = Relation.nary("Q", 1);
        Relation x1 = Relation.nary("B", 1);
        Relation x2 = Relation.nary("A", 1);
        Relation x3 = Relation.nary("QQ", 3);

        List<String> atomlist = Arrays.asList("A", "B", "Q");
        Universe universe = new Universe(atomlist);
        TupleFactory factory = universe.factory();
        Bounds bounds = new Bounds(universe);

        TupleSet x0_upper = factory.noneOf(1);
        x0_upper.add(factory.tuple("Q"));
        bounds.boundExactly(x0, x0_upper);

        TupleSet x1_upper = factory.noneOf(1);
        x1_upper.add(factory.tuple("B"));
        bounds.boundExactly(x1, x1_upper);

        TupleSet x2_upper = factory.noneOf(1);
        x2_upper.add(factory.tuple("A"));
        bounds.boundExactly(x2, x2_upper);

        TupleSet x3_upper = factory.noneOf(3);
        x3_upper.add(factory.tuple("Q").product(factory.tuple("A")).product(factory.tuple("A")));
        x3_upper.add(factory.tuple("Q").product(factory.tuple("B")).product(factory.tuple("B")));
        bounds.bound(x3, x3_upper);

        Expression x7 = x2.product(x2);
        Expression x8 = x0.join(x3);
        Formula x6 = x7.in(x8);
        Formula x5 = x6.not();

        Expression x18 = x1.product(x1);
        Expression x17 = x7.union(x18);
        Expression x16 = x0.product(x17);

        Formula x15 = x3.in(x16);
        Formula x4 = x5.and(x15);

        Solver solver = new Solver();

        solver.options().setSolver(SATFactory.DefaultSAT4J);
        solver.options().setBitwidth(4);
        solver.options().setIntEncoding(Options.IntEncoding.TWOSCOMPLEMENT);

        // System.out.println(bounds);
        // System.out.println(x4);
        Solution sol = solver.solve(x4, bounds);
        assertEquals(sol.outcome(), Solution.Outcome.SATISFIABLE);
        // System.out.println(sol.toString());
    }

    public final void testFelix_10182006() {
        // (some x: one { y: one SIG | true } | true)
        Relation sig = Relation.unary("SIG");
        final Variable x = Variable.unary("x");
        final Variable y = Variable.unary("y");
        final Expression e0 = Formula.TRUE.comprehension(y.oneOf(sig));
        final Formula f0 = Formula.TRUE.forSome(x.oneOf(e0));
        final Universe u = new Universe(Arrays.asList("a0"));
        final Bounds bounds = new Bounds(u);
        bounds.bound(sig, u.factory().allOf(1));
        final Solution s = solver.solve(f0, bounds);
        assertEquals(Solution.Outcome.SATISFIABLE, s.outcome());
    }

    public final void testEmina_10092006() {
        Relation r = Relation.ternary("r");
        final Variable a = Variable.unary("A");
        final Variable b = Variable.unary("B");
        final Variable c = Variable.unary("C");
        final Variable d = Variable.unary("D");
        final Formula f0 = (b.join(a.join(r))).eq(d.join(c.join(r)));
        final Formula f1 = a.in(c).and(b.in(d));
        final Formula f = f0.implies(f1).forAll(a.oneOf(UNIV).and(b.oneOf(UNIV)).and(c.oneOf(UNIV)).and(d.oneOf(UNIV)));
        final Universe u = new Universe(Arrays.asList("a0", "a1"));
        final Bounds bounds = new Bounds(u);
        bounds.bound(r, u.factory().allOf(3));
        // System.out.println(f); System.out.println(bounds);
        solver.options().setSymmetryBreaking(0);
        // solver.options().setFlatten(false);
        final Solution s = solver.solve(f, bounds);
        // System.out.println(s);
        assertEquals(Solution.Outcome.SATISFIABLE, s.outcome());
    }

    public final void testFelix_08142006() {
        Relation x0 = Relation.nary("/nodeOrd/Ord", 1);
        Relation x1 = Relation.nary("/msg/ord/Ord", 1);
        Relation x2 = Relation.nary("/msg/Tick", 1);
        Relation x3 = Relation.nary("/bool/False", 1);
        Relation x4 = Relation.nary("/bool/True", 1);
        Relation x5 = Relation.nary("/bool/Bool", 1);
        Relation x6 = Relation.nary("/RingLeadNodeState", 1);
        Relation x7 = Relation.nary("/msg/NodeState", 1);
        Relation x8 = Relation.nary("/MsgViz", 1);
        Relation x9 = Relation.nary("/msg/Msg", 1);
        Relation x10 = Relation.nary("/RingLeadMsgState", 1);
        Relation x11 = Relation.nary("/msg/MsgState", 1);
        Relation x12 = Relation.nary("/RingLeadNode", 1);
        Relation x13 = Relation.nary("/msg/Node", 1);
        Relation x14 = Relation.nary("/RingLeadNode.rightNeighbor", 2);
        Relation x15 = Relation.nary("/msg/MsgState.from", 2);
        Relation x16 = Relation.nary("/msg/MsgState.to", 2);
        Relation x17 = Relation.nary("/RingLeadMsgState.id", 2);
        Relation x18 = Relation.nary("/msg/Msg.state", 2);
        Relation x19 = Relation.nary("/msg/Msg.sentOn", 2);
        Relation x20 = Relation.nary("/msg/Msg.readOn", 3);
        Relation x21 = Relation.nary("/MsgViz.vFrom", 2);
        Relation x22 = Relation.nary("/MsgViz.vTo", 2);
        Relation x23 = Relation.nary("/MsgViz.vId", 2);
        Relation x24 = Relation.nary("/RingLeadNodeState.leader", 2);
        Relation x25 = Relation.nary("/msg/Tick.state", 3);
        Relation x26 = Relation.nary("/msg/Tick.visible", 3);
        Relation x27 = Relation.nary("/msg/Tick.read", 3);
        Relation x28 = Relation.nary("/msg/Tick.sent", 3);
        Relation x29 = Relation.nary("/msg/Tick.available", 2);
        Relation x30 = Relation.nary("/msg/Tick.needsToSend", 3);

        Relation x31 = Relation.nary("first_", 1);
        Relation x32 = Relation.nary("last_", 1);
        Relation x33 = Relation.nary("next_", 2);
        Relation x34 = Relation.nary("first_", 1);
        Relation x35 = Relation.nary("last_", 1);
        Relation x36 = Relation.nary("next_", 2);

        String[] atoms = {
                          "-1", "-2", "-3", "-4", "-5", "-6", "-7", "-8", "0", "1", "2", "3", "4", "5", "6", "7", "Bool.0", "Bool.1", "Msg.0", "MsgState.0", "Node.0", "NodeState.0", "NodeState.1", "Ord.0", "Ord.1", "Tick.0", "Tick.1", "Tick.2"
        };

        java.util.ArrayList<String> atomlist = new java.util.ArrayList<String>();
        for (String a : atoms)
            atomlist.add(a);
        Universe universe = new Universe(atomlist);
        TupleFactory factory = universe.factory();
        Bounds bounds = new Bounds(universe);

        TupleSet x0_upper = factory.noneOf(1);
        x0_upper.add(factory.tuple("Ord.1"));
        bounds.bound(x0, x0_upper);

        TupleSet x1_upper = factory.noneOf(1);
        x1_upper.add(factory.tuple("Ord.0"));
        bounds.bound(x1, x1_upper);

        TupleSet x2_upper = factory.noneOf(1);
        x2_upper.add(factory.tuple("Tick.0"));
        x2_upper.add(factory.tuple("Tick.1"));
        x2_upper.add(factory.tuple("Tick.2"));
        bounds.boundExactly(x2, x2_upper);

        TupleSet x3_upper = factory.noneOf(1);
        x3_upper.add(factory.tuple("Bool.1"));
        bounds.bound(x3, x3_upper);

        TupleSet x4_upper = factory.noneOf(1);
        x4_upper.add(factory.tuple("Bool.0"));
        bounds.bound(x4, x4_upper);

        TupleSet x5_upper = factory.noneOf(1);
        x5_upper.add(factory.tuple("Bool.0"));
        x5_upper.add(factory.tuple("Bool.1"));
        bounds.bound(x5, x5_upper);

        TupleSet x6_upper = factory.noneOf(1);
        x6_upper.add(factory.tuple("NodeState.0"));
        x6_upper.add(factory.tuple("NodeState.1"));
        bounds.bound(x6, x6_upper);

        TupleSet x7_upper = factory.noneOf(1);
        x7_upper.add(factory.tuple("NodeState.0"));
        x7_upper.add(factory.tuple("NodeState.1"));
        bounds.bound(x7, x7_upper);

        TupleSet x8_upper = factory.noneOf(1);
        x8_upper.add(factory.tuple("Msg.0"));
        bounds.bound(x8, x8_upper);

        TupleSet x9_upper = factory.noneOf(1);
        x9_upper.add(factory.tuple("Msg.0"));
        bounds.bound(x9, x9_upper);

        TupleSet x10_upper = factory.noneOf(1);
        x10_upper.add(factory.tuple("MsgState.0"));
        bounds.bound(x10, x10_upper);

        TupleSet x11_upper = factory.noneOf(1);
        x11_upper.add(factory.tuple("MsgState.0"));
        bounds.bound(x11, x11_upper);

        TupleSet x12_upper = factory.noneOf(1);
        x12_upper.add(factory.tuple("Node.0"));
        bounds.bound(x12, x12_upper);

        TupleSet x13_upper = factory.noneOf(1);
        x13_upper.add(factory.tuple("Node.0"));
        bounds.boundExactly(x13, x13_upper);

        TupleSet x14_upper = factory.noneOf(2);
        x14_upper.add(factory.tuple("Node.0").product(factory.tuple("Node.0")));
        bounds.bound(x14, x14_upper);

        TupleSet x15_upper = factory.noneOf(2);
        x15_upper.add(factory.tuple("MsgState.0").product(factory.tuple("Node.0")));
        bounds.bound(x15, x15_upper);

        TupleSet x16_upper = factory.noneOf(2);
        x16_upper.add(factory.tuple("MsgState.0").product(factory.tuple("Node.0")));
        bounds.bound(x16, x16_upper);

        TupleSet x17_upper = factory.noneOf(2);
        x17_upper.add(factory.tuple("MsgState.0").product(factory.tuple("Node.0")));
        bounds.bound(x17, x17_upper);

        TupleSet x18_upper = factory.noneOf(2);
        x18_upper.add(factory.tuple("Msg.0").product(factory.tuple("MsgState.0")));
        bounds.bound(x18, x18_upper);

        TupleSet x19_upper = factory.noneOf(2);
        x19_upper.add(factory.tuple("Msg.0").product(factory.tuple("Tick.0")));
        x19_upper.add(factory.tuple("Msg.0").product(factory.tuple("Tick.1")));
        x19_upper.add(factory.tuple("Msg.0").product(factory.tuple("Tick.2")));
        bounds.bound(x19, x19_upper);

        TupleSet x20_upper = factory.noneOf(3);
        x20_upper.add(factory.tuple("Msg.0").product(factory.tuple("Node.0")).product(factory.tuple("Tick.0")));
        x20_upper.add(factory.tuple("Msg.0").product(factory.tuple("Node.0")).product(factory.tuple("Tick.1")));
        x20_upper.add(factory.tuple("Msg.0").product(factory.tuple("Node.0")).product(factory.tuple("Tick.2")));
        bounds.bound(x20, x20_upper);

        TupleSet x21_upper = factory.noneOf(2);
        x21_upper.add(factory.tuple("Msg.0").product(factory.tuple("Node.0")));
        bounds.bound(x21, x21_upper);

        TupleSet x22_upper = factory.noneOf(2);
        x22_upper.add(factory.tuple("Msg.0").product(factory.tuple("Node.0")));
        bounds.bound(x22, x22_upper);

        TupleSet x23_upper = factory.noneOf(2);
        x23_upper.add(factory.tuple("Msg.0").product(factory.tuple("Node.0")));
        bounds.bound(x23, x23_upper);

        TupleSet x24_upper = factory.noneOf(2);
        x24_upper.add(factory.tuple("NodeState.0").product(factory.tuple("Bool.0")));
        x24_upper.add(factory.tuple("NodeState.0").product(factory.tuple("Bool.1")));
        x24_upper.add(factory.tuple("NodeState.1").product(factory.tuple("Bool.0")));
        x24_upper.add(factory.tuple("NodeState.1").product(factory.tuple("Bool.1")));
        bounds.bound(x24, x24_upper);

        TupleSet x25_upper = factory.noneOf(3);
        x25_upper.add(factory.tuple("Tick.0").product(factory.tuple("Node.0")).product(factory.tuple("NodeState.0")));
        x25_upper.add(factory.tuple("Tick.0").product(factory.tuple("Node.0")).product(factory.tuple("NodeState.1")));
        x25_upper.add(factory.tuple("Tick.1").product(factory.tuple("Node.0")).product(factory.tuple("NodeState.0")));
        x25_upper.add(factory.tuple("Tick.1").product(factory.tuple("Node.0")).product(factory.tuple("NodeState.1")));
        x25_upper.add(factory.tuple("Tick.2").product(factory.tuple("Node.0")).product(factory.tuple("NodeState.0")));
        x25_upper.add(factory.tuple("Tick.2").product(factory.tuple("Node.0")).product(factory.tuple("NodeState.1")));
        bounds.bound(x25, x25_upper);

        TupleSet x26_upper = factory.noneOf(3);
        x26_upper.add(factory.tuple("Tick.0").product(factory.tuple("Node.0")).product(factory.tuple("Msg.0")));
        x26_upper.add(factory.tuple("Tick.1").product(factory.tuple("Node.0")).product(factory.tuple("Msg.0")));
        x26_upper.add(factory.tuple("Tick.2").product(factory.tuple("Node.0")).product(factory.tuple("Msg.0")));
        bounds.bound(x26, x26_upper);

        TupleSet x27_upper = factory.noneOf(3);
        x27_upper.add(factory.tuple("Tick.0").product(factory.tuple("Node.0")).product(factory.tuple("Msg.0")));
        x27_upper.add(factory.tuple("Tick.1").product(factory.tuple("Node.0")).product(factory.tuple("Msg.0")));
        x27_upper.add(factory.tuple("Tick.2").product(factory.tuple("Node.0")).product(factory.tuple("Msg.0")));
        bounds.bound(x27, x27_upper);

        TupleSet x28_upper = factory.noneOf(3);
        x28_upper.add(factory.tuple("Tick.0").product(factory.tuple("Node.0")).product(factory.tuple("Msg.0")));
        x28_upper.add(factory.tuple("Tick.1").product(factory.tuple("Node.0")).product(factory.tuple("Msg.0")));
        x28_upper.add(factory.tuple("Tick.2").product(factory.tuple("Node.0")).product(factory.tuple("Msg.0")));
        bounds.bound(x28, x28_upper);

        TupleSet x29_upper = factory.noneOf(2);
        x29_upper.add(factory.tuple("Tick.0").product(factory.tuple("Msg.0")));
        x29_upper.add(factory.tuple("Tick.1").product(factory.tuple("Msg.0")));
        x29_upper.add(factory.tuple("Tick.2").product(factory.tuple("Msg.0")));
        bounds.bound(x29, x29_upper);

        TupleSet x30_upper = factory.noneOf(3);
        x30_upper.add(factory.tuple("Tick.0").product(factory.tuple("Node.0")).product(factory.tuple("Msg.0")));
        x30_upper.add(factory.tuple("Tick.1").product(factory.tuple("Node.0")).product(factory.tuple("Msg.0")));
        x30_upper.add(factory.tuple("Tick.2").product(factory.tuple("Node.0")).product(factory.tuple("Msg.0")));
        bounds.bound(x30, x30_upper);

        TupleSet x31_upper = factory.noneOf(1);
        x31_upper.add(factory.tuple("Tick.0"));
        x31_upper.add(factory.tuple("Tick.1"));
        x31_upper.add(factory.tuple("Tick.2"));
        bounds.bound(x31, x31_upper);

        TupleSet x32_upper = factory.noneOf(1);
        x32_upper.add(factory.tuple("Tick.0"));
        x32_upper.add(factory.tuple("Tick.1"));
        x32_upper.add(factory.tuple("Tick.2"));
        bounds.bound(x32, x32_upper);

        TupleSet x33_upper = factory.noneOf(2);
        x33_upper.add(factory.tuple("Tick.0").product(factory.tuple("Tick.0")));
        x33_upper.add(factory.tuple("Tick.0").product(factory.tuple("Tick.1")));
        x33_upper.add(factory.tuple("Tick.0").product(factory.tuple("Tick.2")));
        x33_upper.add(factory.tuple("Tick.1").product(factory.tuple("Tick.0")));
        x33_upper.add(factory.tuple("Tick.1").product(factory.tuple("Tick.1")));
        x33_upper.add(factory.tuple("Tick.1").product(factory.tuple("Tick.2")));
        x33_upper.add(factory.tuple("Tick.2").product(factory.tuple("Tick.0")));
        x33_upper.add(factory.tuple("Tick.2").product(factory.tuple("Tick.1")));
        x33_upper.add(factory.tuple("Tick.2").product(factory.tuple("Tick.2")));
        bounds.bound(x33, x33_upper);

        TupleSet x34_upper = factory.noneOf(1);
        x34_upper.add(factory.tuple("Node.0"));
        bounds.bound(x34, x34_upper);

        TupleSet x35_upper = factory.noneOf(1);
        x35_upper.add(factory.tuple("Node.0"));
        bounds.bound(x35, x35_upper);

        TupleSet x36_upper = factory.noneOf(2);
        x36_upper.add(factory.tuple("Node.0").product(factory.tuple("Node.0")));
        bounds.bound(x36, x36_upper);

        bounds.boundExactly(-8, factory.range(factory.tuple("-8"), factory.tuple("-8")));

        bounds.boundExactly(-7, factory.range(factory.tuple("-7"), factory.tuple("-7")));

        bounds.boundExactly(-6, factory.range(factory.tuple("-6"), factory.tuple("-6")));

        bounds.boundExactly(-5, factory.range(factory.tuple("-5"), factory.tuple("-5")));

        bounds.boundExactly(-4, factory.range(factory.tuple("-4"), factory.tuple("-4")));

        bounds.boundExactly(-3, factory.range(factory.tuple("-3"), factory.tuple("-3")));

        bounds.boundExactly(-2, factory.range(factory.tuple("-2"), factory.tuple("-2")));

        bounds.boundExactly(-1, factory.range(factory.tuple("-1"), factory.tuple("-1")));

        bounds.boundExactly(0, factory.range(factory.tuple("0"), factory.tuple("0")));

        bounds.boundExactly(1, factory.range(factory.tuple("1"), factory.tuple("1")));

        bounds.boundExactly(2, factory.range(factory.tuple("2"), factory.tuple("2")));

        bounds.boundExactly(3, factory.range(factory.tuple("3"), factory.tuple("3")));

        bounds.boundExactly(4, factory.range(factory.tuple("4"), factory.tuple("4")));

        bounds.boundExactly(5, factory.range(factory.tuple("5"), factory.tuple("5")));

        bounds.boundExactly(6, factory.range(factory.tuple("6"), factory.tuple("6")));

        bounds.boundExactly(7, factory.range(factory.tuple("7"), factory.tuple("7")));

        Variable x41 = Variable.nary("@t", 1);
        Expression x44 = x1.product(x32);
        Expression x43 = x1.join(x44);
        Expression x42 = x2.difference(x43);
        Decls x40 = x41.oneOf(x42);
        Expression x48 = x41.join(x25);
        Expression x49 = x43.join(x25);
        Formula x47 = x48.eq(x49);
        Variable x52 = Variable.nary("@r", 2);
        Variable x59 = Variable.nary("VAR<future>", 1);
        Decls x58 = x59.oneOf(x9);
        Expression x61 = x59.join(x19);
        Expression x65 = x1.product(x33);
        Expression x64 = x1.join(x65);
        Expression x63 = x64.closure();
        Expression x62 = x41.join(x63);
        Formula x60 = x61.in(x62);
        Expression x57 = x60.comprehension(x58);
        Expression x56 = x9.difference(x57);
        Variable x68 = Variable.nary("VAR<past>", 1);
        Decls x67 = x68.oneOf(x9);
        Variable x71 = Variable.nary("@n", 1);
        Expression x73 = x68.join(x18);
        Expression x72 = x73.join(x16);
        Decls x70 = x71.oneOf(x72);
        Expression x76 = x68.join(x20);
        Expression x75 = x71.join(x76);
        Expression x81 = x33.transpose();
        Expression x80 = x1.product(x81);
        Expression x79 = x1.join(x80);
        Expression x78 = x79.closure();
        Expression x77 = x41.join(x78);
        Formula x74 = x75.in(x77);
        Formula x69 = x74.forAll(x70);
        Expression x66 = x69.comprehension(x67);
        Expression x55 = x56.difference(x66);
        Expression x83 = x41.join(x26);
        Expression x82 = x13.join(x83);
        Expression x54 = x55.difference(x82);
        Variable x89 = Variable.nary("VAR<future>", 1);
        Decls x88 = x89.oneOf(x9);
        Expression x91 = x89.join(x19);
        Expression x92 = x43.join(x63);
        Formula x90 = x91.in(x92);
        Expression x87 = x90.comprehension(x88);
        Expression x86 = x9.difference(x87);
        Variable x95 = Variable.nary("VAR<past>", 1);
        Decls x94 = x95.oneOf(x9);
        Variable x98 = Variable.nary("@n", 1);
        Expression x100 = x95.join(x18);
        Expression x99 = x100.join(x16);
        Decls x97 = x98.oneOf(x99);
        Expression x103 = x95.join(x20);
        Expression x102 = x98.join(x103);
        Expression x104 = x43.join(x78);
        Formula x101 = x102.in(x104);
        Formula x96 = x101.forAll(x97);
        Expression x93 = x96.comprehension(x94);
        Expression x85 = x86.difference(x93);
        Expression x106 = x43.join(x26);
        Expression x105 = x13.join(x106);
        Expression x84 = x85.difference(x105);
        Expression x53 = x54.product(x84);
        Decls x51 = x52.setOf(x53);
        Variable x117 = Variable.nary("VAR<future>", 1);
        Decls x116 = x117.oneOf(x9);
        Expression x119 = x117.join(x19);
        Formula x118 = x119.in(x62);
        Expression x115 = x118.comprehension(x116);
        Expression x114 = x9.difference(x115);
        Variable x122 = Variable.nary("VAR<past>", 1);
        Decls x121 = x122.oneOf(x9);
        Variable x125 = Variable.nary("@n", 1);
        Expression x127 = x122.join(x18);
        Expression x126 = x127.join(x16);
        Decls x124 = x125.oneOf(x126);
        Expression x130 = x122.join(x20);
        Expression x129 = x125.join(x130);
        Formula x128 = x129.in(x77);
        Formula x123 = x128.forAll(x124);
        Expression x120 = x123.comprehension(x121);
        Expression x113 = x114.difference(x120);
        Expression x112 = x113.difference(x82);
        Variable x136 = Variable.nary("VAR<future>", 1);
        Decls x135 = x136.oneOf(x9);
        Expression x138 = x136.join(x19);
        Formula x137 = x138.in(x92);
        Expression x134 = x137.comprehension(x135);
        Expression x133 = x9.difference(x134);
        Variable x141 = Variable.nary("VAR<past>", 1);
        Decls x140 = x141.oneOf(x9);
        Variable x144 = Variable.nary("@n", 1);
        Expression x146 = x141.join(x18);
        Expression x145 = x146.join(x16);
        Decls x143 = x144.oneOf(x145);
        Expression x149 = x141.join(x20);
        Expression x148 = x144.join(x149);
        Formula x147 = x148.in(x104);
        Formula x142 = x147.forAll(x143);
        Expression x139 = x142.comprehension(x140);
        Expression x132 = x133.difference(x139);
        Expression x131 = x132.difference(x105);
        Expression x111 = x112.product(x131);
        Formula x110 = x52.in(x111);
        Variable x152 = Variable.nary("@", 1);
        Variable x158 = Variable.nary("VAR<future>", 1);
        Decls x157 = x158.oneOf(x9);
        Expression x160 = x158.join(x19);
        Formula x159 = x160.in(x62);
        Expression x156 = x159.comprehension(x157);
        Expression x155 = x9.difference(x156);
        Variable x163 = Variable.nary("VAR<past>", 1);
        Decls x162 = x163.oneOf(x9);
        Variable x166 = Variable.nary("@n", 1);
        Expression x168 = x163.join(x18);
        Expression x167 = x168.join(x16);
        Decls x165 = x166.oneOf(x167);
        Expression x171 = x163.join(x20);
        Expression x170 = x166.join(x171);
        Formula x169 = x170.in(x77);
        Formula x164 = x169.forAll(x165);
        Expression x161 = x164.comprehension(x162);
        Expression x154 = x155.difference(x161);
        Expression x153 = x154.difference(x82);
        Decls x151 = x152.oneOf(x153);
        Expression x174 = x152.join(x52);
        Formula x173 = x174.one();
        Variable x181 = Variable.nary("VAR<future>", 1);
        Decls x180 = x181.oneOf(x9);
        Expression x183 = x181.join(x19);
        Formula x182 = x183.in(x92);
        Expression x179 = x182.comprehension(x180);
        Expression x178 = x9.difference(x179);
        Variable x186 = Variable.nary("VAR<past>", 1);
        Decls x185 = x186.oneOf(x9);
        Variable x189 = Variable.nary("@n", 1);
        Expression x191 = x186.join(x18);
        Expression x190 = x191.join(x16);
        Decls x188 = x189.oneOf(x190);
        Expression x194 = x186.join(x20);
        Expression x193 = x189.join(x194);
        Formula x192 = x193.in(x104);
        Formula x187 = x192.forAll(x188);
        Expression x184 = x187.comprehension(x185);
        Expression x177 = x178.difference(x184);
        Expression x176 = x177.difference(x105);
        Formula x175 = x174.in(x176);
        Formula x172 = x173.and(x175);
        Formula x150 = x172.forAll(x151);
        Formula x109 = x110.and(x150);
        Variable x197 = Variable.nary("@", 1);
        Decls x196 = x197.oneOf(x176);
        Expression x200 = x52.join(x197);
        Formula x199 = x200.one();
        Formula x201 = x200.in(x153);
        Formula x198 = x199.and(x201);
        Formula x195 = x198.forAll(x196);
        Formula x108 = x109.and(x195);
        Variable x204 = Variable.nary("@m1", 1);
        Expression x205 = x52.join(Expression.UNIV);
        Decls x203 = x204.oneOf(x205);
        Expression x209 = x9.product(Expression.UNIV);
        Expression x208 = x209.intersection(x18);
        Expression x207 = x204.join(x208);
        Expression x211 = x204.join(x52);
        Expression x210 = x211.join(x18);
        Formula x206 = x207.eq(x210);
        Formula x202 = x206.forAll(x203);
        Formula x107 = x108.and(x202);
        Formula x50 = x107.forSome(x51);
        Formula x46 = x47.and(x50);
        Variable x214 = Variable.nary("@r", 2);
        Expression x215 = x82.product(x105);
        Decls x213 = x214.setOf(x215);
        Formula x219 = x214.in(x215);
        Variable x222 = Variable.nary("@", 1);
        Decls x221 = x222.oneOf(x82);
        Expression x225 = x222.join(x214);
        Formula x224 = x225.one();
        Formula x226 = x225.in(x105);
        Formula x223 = x224.and(x226);
        Formula x220 = x223.forAll(x221);
        Formula x218 = x219.and(x220);
        Variable x229 = Variable.nary("@", 1);
        Decls x228 = x229.oneOf(x105);
        Expression x232 = x214.join(x229);
        Formula x231 = x232.one();
        Formula x233 = x232.in(x82);
        Formula x230 = x231.and(x233);
        Formula x227 = x230.forAll(x228);
        Formula x217 = x218.and(x227);
        Variable x236 = Variable.nary("@m1", 1);
        Expression x237 = x214.join(Expression.UNIV);
        Decls x235 = x236.oneOf(x237);
        Expression x239 = x236.join(x208);
        Expression x241 = x236.join(x214);
        Expression x240 = x241.join(x18);
        Formula x238 = x239.eq(x240);
        Formula x234 = x238.forAll(x235);
        Formula x216 = x217.and(x234);
        Formula x212 = x216.forSome(x213);
        Formula x45 = x46.and(x212);
        Formula x39 = x45.forSome(x40);
        Variable x244 = Variable.nary("@t", 1);
        Decls x243 = x244.oneOf(x2);
        Variable x248 = Variable.nary("@n", 1);
        Decls x247 = x248.oneOf(x13);
        Expression x252 = x244.join(x25);
        Expression x251 = x248.join(x252);
        Expression x250 = x251.join(x24);
        Formula x249 = x250.eq(x4);
        Formula x246 = x249.forSome(x247);
        Formula x245 = x246.not();
        Formula x242 = x245.forAll(x243);
        Formula x38 = x39.and(x242);
        Variable x256 = Variable.nary("@this", 1);
        Decls x255 = x256.oneOf(x2);
        Expression x260 = x256.join(x25);
        Expression x261 = x13.product(x7);
        Formula x259 = x260.in(x261);
        Variable x264 = Variable.nary("@", 1);
        Decls x263 = x264.oneOf(x13);
        Expression x267 = x264.join(x260);
        Formula x266 = x267.one();
        Formula x268 = x267.in(x7);
        Formula x265 = x266.and(x268);
        Formula x262 = x265.forAll(x263);
        Formula x258 = x259.and(x262);
        Variable x271 = Variable.nary("@", 1);
        Decls x270 = x271.oneOf(x7);
        Expression x273 = x260.join(x271);
        Formula x272 = x273.in(x13);
        Formula x269 = x272.forAll(x270);
        Formula x257 = x258.and(x269);
        Formula x254 = x257.forAll(x255);
        Expression x277 = x13.product(x9);
        Expression x276 = x2.product(x277);
        Formula x275 = x30.in(x276);
        Expression x280 = x2.product(x9);
        Formula x279 = x29.in(x280);
        Formula x282 = x28.in(x276);
        Formula x284 = x27.in(x276);
        Formula x286 = x26.in(x276);
        Expression x290 = x2.product(Expression.UNIV);
        Expression x289 = x290.product(Expression.UNIV);
        Formula x288 = x25.in(x289);
        Variable x294 = Variable.nary("@this", 1);
        Decls x293 = x294.oneOf(x9);
        Expression x300 = x294.join(x20);
        Expression x299 = x300.join(x2);
        Expression x302 = x294.join(x18);
        Expression x301 = x302.join(x16);
        Formula x298 = x299.in(x301);
        Formula x304 = x302.one();
        Formula x305 = x302.in(x11);
        Formula x303 = x304.and(x305);
        Formula x297 = x298.and(x303);
        Expression x308 = x294.join(x19);
        Formula x307 = x308.one();
        Formula x309 = x308.in(x2);
        Formula x306 = x307.and(x309);
        Formula x296 = x297.and(x306);
        Expression x313 = x13.product(x2);
        Formula x312 = x300.in(x313);
        Variable x316 = Variable.nary("@", 1);
        Decls x315 = x316.oneOf(x13);
        Expression x319 = x316.join(x300);
        Formula x318 = x319.lone();
        Formula x320 = x319.in(x2);
        Formula x317 = x318.and(x320);
        Formula x314 = x317.forAll(x315);
        Formula x311 = x312.and(x314);
        Variable x323 = Variable.nary("@", 1);
        Decls x322 = x323.oneOf(x2);
        Expression x325 = x300.join(x323);
        Formula x324 = x325.in(x13);
        Formula x321 = x324.forAll(x322);
        Formula x310 = x311.and(x321);
        Formula x295 = x296.and(x310);
        Formula x292 = x295.forAll(x293);
        Expression x328 = x209.product(Expression.UNIV);
        Formula x327 = x20.in(x328);
        Formula x330 = x19.in(x209);
        Formula x332 = x18.in(x209);
        Variable x336 = Variable.nary("@this", 1);
        Decls x335 = x336.oneOf(x11);
        Expression x339 = x336.join(x15);
        Formula x338 = x339.one();
        Formula x340 = x339.in(x13);
        Formula x337 = x338.and(x340);
        Formula x334 = x337.forAll(x335);
        Expression x343 = x11.product(x13);
        Formula x342 = x16.in(x343);
        Expression x346 = x11.product(Expression.UNIV);
        Formula x345 = x15.in(x346);
        Formula x348 = x27.in(x26);
        Expression x352 = x2.join(x28);
        Expression x351 = x13.join(x352);
        Formula x350 = x9.in(x351);
        Expression x360 = x1.product(x31);
        Expression x359 = x1.join(x360);
        Expression x358 = x359.join(x26);
        Expression x357 = x13.join(x358);
        Formula x356 = x357.no();
        Variable x363 = Variable.nary("@pre", 1);
        Decls x362 = x363.oneOf(x42);
        Expression x366 = x363.join(x64);
        Expression x365 = x366.join(x29);
        Expression x368 = x363.join(x29);
        Expression x370 = x363.join(x28);
        Expression x369 = x13.join(x370);
        Expression x367 = x368.difference(x369);
        Formula x364 = x365.eq(x367);
        Formula x361 = x364.forAll(x362);
        Formula x355 = x356.and(x361);
        Variable x373 = Variable.nary("@t", 1);
        Decls x372 = x373.oneOf(x2);
        Expression x382 = x373.join(x28);
        Expression x381 = x13.join(x382);
        Expression x383 = x373.join(x29);
        Formula x380 = x381.in(x383);
        Expression x385 = x381.join(x19);
        Formula x384 = x385.in(x373);
        Formula x379 = x380.and(x384);
        Expression x390 = x373.join(x27);
        Expression x389 = x13.join(x390);
        Expression x388 = x389.join(x20);
        Expression x387 = x13.join(x388);
        Formula x386 = x387.in(x373);
        Formula x378 = x379.and(x386);
        Formula x391 = x381.eq(x381);
        Formula x377 = x378.and(x391);
        Variable x394 = Variable.nary("@n", 1);
        Decls x393 = x394.oneOf(x13);
        Variable x397 = Variable.nary("@m", 1);
        Decls x396 = x397.oneOf(x9);
        Expression x401 = x397.join(x20);
        Expression x400 = x394.join(x401);
        Formula x399 = x400.eq(x373);
        Expression x403 = x394.join(x390);
        Formula x402 = x397.in(x403);
        Formula x398 = x399.implies(x402);
        Formula x395 = x398.forAll(x396);
        Formula x392 = x395.forAll(x393);
        Formula x376 = x377.and(x392);
        Variable x406 = Variable.nary("@n", 1);
        Decls x405 = x406.oneOf(x13);
        Expression x410 = x406.join(x382);
        Expression x409 = x410.join(x18);
        Expression x408 = x409.join(x15);
        Formula x407 = x408.in(x406);
        Formula x404 = x407.forAll(x405);
        Formula x375 = x376.and(x404);
        Variable x413 = Variable.nary("@n", 1);
        Decls x412 = x413.oneOf(x13);
        Variable x416 = Variable.nary("@m", 1);
        Decls x415 = x416.oneOf(x9);
        Expression x421 = x373.join(x26);
        Expression x420 = x413.join(x421);
        Formula x419 = x416.in(x420);
        Expression x425 = x416.join(x18);
        Expression x424 = x425.join(x16);
        Formula x423 = x413.in(x424);
        Expression x427 = x416.join(x19);
        Expression x428 = x373.join(x78);
        Formula x426 = x427.in(x428);
        Formula x422 = x423.and(x426);
        Formula x418 = x419.implies(x422);
        Expression x431 = x413.join(x390);
        Formula x430 = x416.in(x431);
        Expression x436 = x373.join(x63);
        Expression x435 = x436.join(x26);
        Expression x434 = x413.join(x435);
        Formula x433 = x416.in(x434);
        Formula x432 = x433.not();
        Formula x429 = x430.implies(x432);
        Formula x417 = x418.and(x429);
        Formula x414 = x417.forAll(x415);
        Formula x411 = x414.forAll(x412);
        Formula x374 = x375.and(x411);
        Formula x371 = x374.forAll(x372);
        Formula x354 = x355.and(x371);
        Variable x440 = Variable.nary("@this", 1);
        Decls x439 = x440.oneOf(x6);
        Expression x443 = x440.join(x24);
        Formula x442 = x443.one();
        Formula x444 = x443.in(x5);
        Formula x441 = x442.and(x444);
        Formula x438 = x441.forAll(x439);
        Expression x447 = x6.product(Expression.UNIV);
        Formula x446 = x24.in(x447);
        Variable x451 = Variable.nary("@this", 1);
        Decls x450 = x451.oneOf(x8);
        Expression x455 = x451.join(x21);
        Formula x454 = x455.one();
        Formula x456 = x455.in(x13);
        Formula x453 = x454.and(x456);
        Expression x459 = x451.join(x23);
        Formula x458 = x459.one();
        Formula x460 = x459.in(x13);
        Formula x457 = x458.and(x460);
        Formula x452 = x453.and(x457);
        Formula x449 = x452.forAll(x450);
        Expression x463 = x8.product(Expression.UNIV);
        Formula x462 = x23.in(x463);
        Expression x466 = x8.product(x13);
        Formula x465 = x22.in(x466);
        Formula x468 = x21.in(x463);
        Variable x472 = Variable.nary("@this", 1);
        Decls x471 = x472.oneOf(x10);
        Expression x475 = x472.join(x17);
        Formula x474 = x475.one();
        Formula x476 = x475.in(x13);
        Formula x473 = x474.and(x476);
        Formula x470 = x473.forAll(x471);
        Expression x479 = x10.product(Expression.UNIV);
        Formula x478 = x17.in(x479);
        Variable x483 = Variable.nary("@this", 1);
        Decls x482 = x483.oneOf(x12);
        Expression x486 = x483.join(x14);
        Formula x485 = x486.one();
        Formula x487 = x486.in(x13);
        Formula x484 = x485.and(x487);
        Formula x481 = x484.forAll(x482);
        Expression x490 = x12.product(Expression.UNIV);
        Formula x489 = x14.in(x490);
        Formula x494 = x12.eq(x13);
        Formula x495 = x10.eq(x11);
        Formula x493 = x494.and(x495);
        Formula x496 = x6.eq(x7);
        Formula x492 = x493.and(x496);
        Variable x500 = Variable.nary("@n", 1);
        Decls x499 = x500.oneOf(x13);
        Variable x504 = Variable.nary("@t", 1);
        Decls x503 = x504.oneOf(x42);
        Formula x507 = x504.eq(x359);
        Expression x514 = x504.join(x28);
        Expression x513 = x500.join(x514);
        Formula x512 = x513.one();
        Expression x518 = x504.join(x30);
        Expression x517 = x500.join(x518);
        IntExpression x516 = x517.count();
        IntExpression x519 = IntConstant.constant(1);
        Formula x515 = x516.eq(x519);
        Formula x511 = x512.and(x515);
        Expression x522 = x513.join(x18);
        Expression x521 = x522.join(x16);
        Expression x523 = x500.join(x14);
        Formula x520 = x521.eq(x523);
        Formula x510 = x511.and(x520);
        Expression x525 = x522.join(x17);
        Formula x524 = x525.eq(x500);
        Formula x509 = x510.and(x524);
        Expression x530 = x504.join(x64);
        Expression x529 = x530.join(x25);
        Expression x528 = x500.join(x529);
        Expression x527 = x528.join(x24);
        Formula x526 = x527.eq(x3);
        Formula x508 = x509.and(x526);
        Formula x506 = x507.implies(x508);
        Formula x532 = x507.not();
        Expression x539 = x504.join(x27);
        Expression x538 = x500.join(x539);
        Expression x541 = x504.join(x26);
        Expression x540 = x500.join(x541);
        Formula x537 = x538.eq(x540);
        Variable x544 = Variable.nary("@received", 1);
        Decls x543 = x544.oneOf(x538);
        Expression x548 = x544.join(x18);
        Expression x547 = x548.join(x17);
        Expression x552 = x0.product(x36);
        Expression x551 = x0.join(x552);
        Expression x550 = x551.closure();
        Expression x549 = x500.join(x550);
        Formula x546 = x547.in(x549);
        Variable x557 = Variable.nary("@weSend", 1);
        Decls x556 = x557.oneOf(x513);
        Variable x559 = Variable.nary("@weSend", 1);
        Decls x558 = x559.oneOf(x513);
        Decls x555 = x556.and(x558);
        Expression x565 = x557.join(x18);
        Expression x564 = x565.join(x17);
        Formula x563 = x564.eq(x547);
        Expression x567 = x565.join(x16);
        Formula x566 = x567.eq(x523);
        Formula x562 = x563.and(x566);
        Expression x571 = x559.join(x18);
        Expression x570 = x571.join(x17);
        Formula x569 = x570.eq(x547);
        Expression x573 = x571.join(x16);
        Formula x572 = x573.eq(x523);
        Formula x568 = x569.and(x572);
        Formula x561 = x562.and(x568);
        Formula x574 = x557.eq(x559);
        Formula x560 = x561.implies(x574);
        Formula x554 = x560.forAll(x555);
        Variable x577 = Variable.nary("@weSend", 1);
        Decls x576 = x577.oneOf(x513);
        Expression x581 = x577.join(x18);
        Expression x580 = x581.join(x17);
        Formula x579 = x580.eq(x547);
        Expression x583 = x581.join(x16);
        Formula x582 = x583.eq(x523);
        Formula x578 = x579.and(x582);
        Formula x575 = x578.forSome(x576);
        Formula x553 = x554.and(x575);
        Formula x545 = x546.implies(x553);
        Formula x542 = x545.forAll(x543);
        Formula x536 = x537.and(x542);
        Variable x586 = Variable.nary("@weSend", 1);
        Decls x585 = x586.oneOf(x513);
        Expression x591 = x586.join(x18);
        Expression x590 = x591.join(x17);
        Formula x589 = x590.in(x549);
        Expression x594 = x538.join(x18);
        Expression x593 = x594.join(x17);
        Formula x592 = x590.in(x593);
        Formula x588 = x589.and(x592);
        Expression x596 = x591.join(x16);
        Formula x595 = x596.eq(x523);
        Formula x587 = x588.and(x595);
        Formula x584 = x587.forAll(x585);
        Formula x535 = x536.and(x584);
        Variable x601 = Variable.nary("VAR<m>", 1);
        Decls x600 = x601.oneOf(x538);
        Expression x604 = x601.join(x18);
        Expression x603 = x604.join(x17);
        Formula x602 = x603.in(x549);
        Expression x599 = x602.comprehension(x600);
        IntExpression x598 = x599.count();
        Formula x597 = x516.eq(x598);
        Formula x534 = x535.and(x597);
        Formula x606 = x527.eq(x4);
        Expression x611 = x504.join(x25);
        Expression x610 = x500.join(x611);
        Expression x609 = x610.join(x24);
        Formula x608 = x609.eq(x4);
        Formula x612 = x500.in(x593);
        Formula x607 = x608.or(x612);
        Formula x605 = x606.iff(x607);
        Formula x533 = x534.and(x605);
        Formula x531 = x532.implies(x533);
        Formula x505 = x506.and(x531);
        Formula x502 = x505.forAll(x503);
        Expression x618 = x43.join(x27);
        Expression x617 = x500.join(x618);
        Expression x619 = x500.join(x106);
        Formula x616 = x617.eq(x619);
        Variable x622 = Variable.nary("@received", 1);
        Decls x621 = x622.oneOf(x617);
        Expression x626 = x622.join(x18);
        Expression x625 = x626.join(x17);
        Formula x624 = x625.in(x549);
        Variable x631 = Variable.nary("@weSend", 1);
        Expression x633 = x43.join(x28);
        Expression x632 = x500.join(x633);
        Decls x630 = x631.oneOf(x632);
        Variable x635 = Variable.nary("@weSend", 1);
        Decls x634 = x635.oneOf(x632);
        Decls x629 = x630.and(x634);
        Expression x641 = x631.join(x18);
        Expression x640 = x641.join(x17);
        Formula x639 = x640.eq(x625);
        Expression x643 = x641.join(x16);
        Formula x642 = x643.eq(x523);
        Formula x638 = x639.and(x642);
        Expression x647 = x635.join(x18);
        Expression x646 = x647.join(x17);
        Formula x645 = x646.eq(x625);
        Expression x649 = x647.join(x16);
        Formula x648 = x649.eq(x523);
        Formula x644 = x645.and(x648);
        Formula x637 = x638.and(x644);
        Formula x650 = x631.eq(x635);
        Formula x636 = x637.implies(x650);
        Formula x628 = x636.forAll(x629);
        Variable x653 = Variable.nary("@weSend", 1);
        Decls x652 = x653.oneOf(x632);
        Expression x657 = x653.join(x18);
        Expression x656 = x657.join(x17);
        Formula x655 = x656.eq(x625);
        Expression x659 = x657.join(x16);
        Formula x658 = x659.eq(x523);
        Formula x654 = x655.and(x658);
        Formula x651 = x654.forSome(x652);
        Formula x627 = x628.and(x651);
        Formula x623 = x624.implies(x627);
        Formula x620 = x623.forAll(x621);
        Formula x615 = x616.and(x620);
        Variable x662 = Variable.nary("@weSend", 1);
        Decls x661 = x662.oneOf(x632);
        Expression x667 = x662.join(x18);
        Expression x666 = x667.join(x17);
        Formula x665 = x666.in(x549);
        Expression x670 = x617.join(x18);
        Expression x669 = x670.join(x17);
        Formula x668 = x666.in(x669);
        Formula x664 = x665.and(x668);
        Expression x672 = x667.join(x16);
        Formula x671 = x672.eq(x523);
        Formula x663 = x664.and(x671);
        Formula x660 = x663.forAll(x661);
        Formula x614 = x615.and(x660);
        Expression x676 = x43.join(x30);
        Expression x675 = x500.join(x676);
        IntExpression x674 = x675.count();
        Variable x680 = Variable.nary("VAR<m>", 1);
        Decls x679 = x680.oneOf(x617);
        Expression x683 = x680.join(x18);
        Expression x682 = x683.join(x17);
        Formula x681 = x682.in(x549);
        Expression x678 = x681.comprehension(x679);
        IntExpression x677 = x678.count();
        Formula x673 = x674.eq(x677);
        Formula x613 = x614.and(x673);
        Formula x501 = x502.and(x613);
        Formula x498 = x501.forAll(x499);
        Variable x687 = Variable.nary("@n", 1);
        Decls x686 = x687.oneOf(x13);
        Expression x691 = x359.join(x25);
        Expression x690 = x687.join(x691);
        Expression x689 = x690.join(x24);
        Formula x688 = x689.eq(x3);
        Formula x685 = x688.forAll(x686);
        Formula x696 = x8.eq(x9);
        Expression x698 = x18.join(x15);
        Formula x697 = x21.eq(x698);
        Formula x695 = x696.and(x697);
        Expression x700 = x18.join(x16);
        Formula x699 = x22.eq(x700);
        Formula x694 = x695.and(x699);
        Expression x702 = x18.join(x17);
        Formula x701 = x23.eq(x702);
        Formula x693 = x694.and(x701);
        Formula x706 = x13.one();
        Variable x709 = Variable.nary("@n", 1);
        Decls x708 = x709.oneOf(x13);
        Expression x712 = x709.join(x14);
        Formula x711 = x709.eq(x712);
        Formula x710 = x711.not();
        Formula x707 = x710.forAll(x708);
        Formula x705 = x706.or(x707);
        Variable x715 = Variable.nary("@n", 1);
        Decls x714 = x715.oneOf(x13);
        Expression x718 = x14.closure();
        Expression x717 = x715.join(x718);
        Formula x716 = x13.in(x717);
        Formula x713 = x716.forAll(x714);
        Formula x704 = x705.and(x713);
        Formula x720 = x0.one();
        Formula x722 = x1.one();
        Formula x724 = x3.one();
        Formula x726 = x4.one();
        Expression x729 = x4.union(x3);
        Formula x728 = x729.eq(x5);
        Formula x731 = x6.in(x7);
        Formula x733 = x8.in(x9);
        Formula x735 = x10.in(x11);
        Formula x737 = x12.in(x13);
        Formula x739 = x36.totalOrder(x13, x34, x35);
        Formula x740 = x33.totalOrder(x2, x31, x32);
        Formula x738 = x739.and(x740);
        Formula x736 = x737.and(x738);
        Formula x734 = x735.and(x736);
        Formula x732 = x733.and(x734);
        Formula x730 = x731.and(x732);
        Formula x727 = x728.and(x730);
        Formula x725 = x726.and(x727);
        Formula x723 = x724.and(x725);
        Formula x721 = x722.and(x723);
        Formula x719 = x720.and(x721);
        Formula x703 = x704.and(x719);
        Formula x692 = x693.and(x703);
        Formula x684 = x685.and(x692);
        Formula x497 = x498.and(x684);
        Formula x491 = x492.and(x497);
        Formula x488 = x489.and(x491);
        Formula x480 = x481.and(x488);
        Formula x477 = x478.and(x480);
        Formula x469 = x470.and(x477);
        Formula x467 = x468.and(x469);
        Formula x464 = x465.and(x467);
        Formula x461 = x462.and(x464);
        Formula x448 = x449.and(x461);
        Formula x445 = x446.and(x448);
        Formula x437 = x438.and(x445);
        Formula x353 = x354.and(x437);
        Formula x349 = x350.and(x353);
        Formula x347 = x348.and(x349);
        Formula x344 = x345.and(x347);
        Formula x341 = x342.and(x344);
        Formula x333 = x334.and(x341);
        Formula x331 = x332.and(x333);
        Formula x329 = x330.and(x331);
        Formula x326 = x327.and(x329);
        Formula x291 = x292.and(x326);
        Formula x287 = x288.and(x291);
        Formula x285 = x286.and(x287);
        Formula x283 = x284.and(x285);
        Formula x281 = x282.and(x283);
        Formula x278 = x279.and(x281);
        Formula x274 = x275.and(x278);
        Formula x253 = x254.and(x274);
        Formula x37 = x38.and(x253);

        Solver solver = new Solver();
        // solver.options().setSolver(SATFactory.ZChaff);
        solver.options().setSolver(SATFactory.DefaultSAT4J);
        solver.options().setBitwidth(4);
        solver.options().setIntEncoding(Options.IntEncoding.TWOSCOMPLEMENT);
        // System.out.println(x37);
        try {
            Solution sol = solver.solve(x37, bounds);
            assertNotNull(sol.instance());
        } catch (HigherOrderDeclException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        } catch (UnboundLeafException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }

    }

    public final void testFelix_08022006() {
        Relation x = Relation.nary("P", 1);

        String[] atoms = {
                          "-8", "-7", "-6", "-5", "-4", "-3", "-2", "-1", "0", "1", "2", "3", "4", "5", "6", "7"
        };

        java.util.ArrayList<String> atomlist = new java.util.ArrayList<String>();
        for (String a : atoms)
            atomlist.add(a);
        Universe universe = new Universe(atomlist);
        TupleFactory factory = universe.factory();
        Bounds bounds = new Bounds(universe);

        for (int i = -8; i <= 7; i++)
            bounds.boundExactly(i, factory.setOf(String.valueOf(i)));

        bounds.bound(x, factory.allOf(1));

        Formula f = x.in(Expression.INTS).and(x.some());

        // System.out.println(bounds);

        Solver solver = new Solver();
        // solver.options().setSolver(SATFactory.ZChaff);
        solver.options().setSolver(SATFactory.DefaultSAT4J);
        solver.options().setBitwidth(4);
        solver.options().setIntEncoding(Options.IntEncoding.TWOSCOMPLEMENT);
        Solution sol;
        try {
            sol = solver.solve(f, bounds);
            assertNotNull(sol.instance());
        } catch (HigherOrderDeclException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        } catch (UnboundLeafException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }

    }

    public final void testVincent_03182006_reduced() {
        final Relation pCourses = Relation.binary("pCourses"), prereqs = Relation.binary("prereqs");
        final List<String> atoms = new ArrayList<String>(14);
        atoms.add("6.002");
        atoms.add("8.02");
        atoms.add("6.003");
        atoms.add("6.001");
        atoms.add("[8.02]");
        atoms.add("[6.001]");
        atoms.add("[]");
        final Universe u = new Universe(atoms);
        final Bounds b = new Bounds(u);
        final TupleFactory f = u.factory();

        b.bound(pCourses, f.setOf(f.tuple("[8.02]", "8.02"), f.tuple("[6.001]", "6.001")));

        b.bound(prereqs, f.setOf(f.tuple("6.002", "[8.02]"), f.tuple("8.02", "[]"), f.tuple("6.003", "[6.001]"), f.tuple("6.001", "[]")));

        // System.out.println(u);
        solver.options().setSolver(SATFactory.DefaultSAT4J);
        Solution solution = solver.solve((pCourses.some()).and(prereqs.some()), b);
        // System.out.println(solution); // SATISFIABLE
        assertEquals(solution.outcome(), Solution.Outcome.SATISFIABLE);

    }

    public final void testVincent_03182006() {
        final Relation cAttributes = Relation.binary("cAttributes"), Int = Relation.unary("Integer"),
                        c6001 = Relation.unary("6.001"), one = Relation.unary("ONE"),
                        prereqsetUsed = Relation.binary("prereqsetUsed"), Course = Relation.unary("Course"),
                        CardinalityGrouping = Relation.unary("CardinalityGrouping"), pCourses = Relation.binary("pCourses"),
                        dec = Relation.binary("dec"), c6002 = Relation.unary("6.002"), greater = Relation.binary("greater"),
                        size = Relation.binary("size"), less = Relation.binary("less"),
                        sAttributes = Relation.binary("sAttributes"), PrereqSet = Relation.unary("PrereqSet"),
                        inc = Relation.binary("inc"), next = Relation.binary("next"), equal = Relation.binary("equal"),
                        Semester = Relation.unary("Semester"), index = Relation.ternary("index"),
                        sCourses = Relation.binary("sCourses"), prev = Relation.binary("prev"),
                        prereqs = Relation.binary("prereqs");
        // [6.002, 8.02, 6.003, 6.001, Spring 2006, Fall 2006, [8.02], [6.001],
        // [], Spring, Even, Fall, 1, 2]
        final List<String> atoms = new ArrayList<String>(14);
        atoms.add("6.002");
        atoms.add("8.02");
        atoms.add("6.003");
        atoms.add("6.001");
        atoms.add("Spring 2006");
        atoms.add("Fall 2006");
        atoms.add("[8.02]");
        atoms.add("[6.001]");
        atoms.add("[]");
        atoms.add("Spring");
        atoms.add("Even");
        atoms.add("Fall");
        atoms.add("1");
        atoms.add("2");
        final Universe u = new Universe(atoms);
        final Bounds b = new Bounds(u);
        final TupleFactory f = u.factory();

        b.bound(cAttributes, f.noneOf(2));
        b.boundExactly(Int, f.range(f.tuple("1"), f.tuple("2")));
        b.boundExactly(c6001, f.setOf(f.tuple("6.001")));
        b.boundExactly(one, f.setOf(f.tuple("1")));
        b.bound(prereqsetUsed, f.setOf(f.tuple("6.002", "[8.02]"), f.tuple("8.02", "[]"), f.tuple("6.003", "[6.001]"), f.tuple("6.001", "[]")));
        b.bound(Course, f.range(f.tuple("6.002"), f.tuple("6.001")));
        b.bound(CardinalityGrouping, f.noneOf(1));
        b.boundExactly(pCourses, f.setOf(f.tuple("[8.02]", "8.02"), f.tuple("[6.001]", "6.001")));
        b.boundExactly(dec, f.setOf(f.tuple("2", "1")));
        b.boundExactly(greater, b.upperBound(dec));
        b.bound(size, f.noneOf(2));
        b.boundExactly(c6002, f.setOf(f.tuple("6.002")));
        b.boundExactly(less, f.setOf(f.tuple("1", "2")));
        b.boundExactly(sAttributes, f.setOf(f.tuple("Spring 2006", "Spring"), f.tuple("Spring 2006", "Even"), f.tuple("Fall 2006", "Even"), f.tuple("Fall 2006", "Fall")));
        b.boundExactly(PrereqSet, f.setOf("[8.02]", "[6.001]", "[]"));
        b.boundExactly(inc, b.upperBound(less));
        b.boundExactly(next, f.setOf(f.tuple("Spring 2006", "Fall 2006")));
        b.boundExactly(equal, f.setOf(f.tuple("1", "1"), f.tuple("2", "2")));
        b.boundExactly(Semester, f.setOf("Spring 2006", "Fall 2006"));
        b.bound(index, f.noneOf(3));
        b.bound(sCourses, f.range(f.tuple("Spring 2006"), f.tuple("Fall 2006")).product(f.range(f.tuple("6.002"), f.tuple("6.001"))));
        b.boundExactly(prev, f.setOf(f.tuple("Fall 2006", "Spring 2006")));
        b.boundExactly(prereqs, f.setOf(f.tuple("6.002", "[8.02]"), f.tuple("8.02", "[]"), f.tuple("6.003", "[6.001]"), f.tuple("6.001", "[]")));
        // for(Relation r : b.relations()) {
        // System.out.println(r + " " + r.arity() + " " + b.lowerBound(r) + " ;
        // " + b.upperBound(r));
        // }
        // System.out.println(u);

        final Formula f0 = sCourses.in(Semester.product(Course));
        final Formula f1 = size.function(CardinalityGrouping, Int);
        final Formula f2 = prereqsetUsed.function(Semester.join(sCourses), PrereqSet);
        final Formula f3 = prereqsetUsed.in(prereqs);
        final Variable s = Variable.unary("s");
        final Expression e0 = s.join(sCourses).join(prereqsetUsed).join(pCourses);
        final Expression e1 = s.join(prev.closure()).join(sCourses);
        final Formula f4 = e0.in(e1).forAll(s.oneOf(Semester));
        final Formula f5 = c6002.in(Semester.join(sCourses));
        final Variable e = Variable.unary("e");
        final Expression e3 = Semester.join(sCourses).difference(e);
        final Formula f60 = c6002.in(e3);
        final Formula f61 = e3.join(prereqsetUsed).join(pCourses).in(e3);
        final Formula f6 = (f60.and(f61)).not().forAll(e.oneOf(Semester.join(sCourses)));
        final Variable c = Variable.unary("c");
        final Formula f7 = c.join(cAttributes).in(s.join(sAttributes)).forAll(c.oneOf(s.join(sCourses))).forAll(s.oneOf(Semester));
        final Variable s1 = Variable.unary("s1"), s2 = Variable.unary("s2");
        final Formula f8 = s1.join(sCourses).intersection(s2.join(sCourses)).no().forAll(s2.oneOf(Semester.difference(s1))).forAll(s1.oneOf(Semester));
        final Formula f9 = c6001.intersection(Semester.join(sCourses)).no();

        final Formula x = f0.and(f1).and(f2).and(f3).and(f4).and(f5).and(f6).and(f7).and(f8);
        final Formula y = x.and(f9);

        // System.out.println(x);
        // System.out.println(y);

        solver.options().setSolver(SATFactory.DefaultSAT4J);
        Solution solution = solver.solve(x, b);
        // System.out.println(solution); // SATISFIABLE
        assertEquals(solution.outcome(), Solution.Outcome.SATISFIABLE);

        Solution solution2 = solver.solve(y, b);
        // System.out.println(solution2); // SATISFIABLE!!!???
        // System.out.println((new
        // Evaluator(solution2.instance())).evaluate(x));
        assertEquals(solution2.outcome(), Solution.Outcome.SATISFIABLE);

    }

    public final void testGreg_03032006() {
        Relation r = Relation.binary("r");
        Universe univ = new Universe(Collections.singleton("o"));
        Bounds bounds = new Bounds(univ);
        bounds.bound(r, univ.factory().allOf(2));

        assertEquals(Solution.Outcome.SATISFIABLE, solver.solve(r.some(), bounds).outcome());

    }

    public final void testGreg_02192006() {
        Relation r1 = Relation.unary("r1");
        Relation r2 = Relation.unary("r2");
        Relation r3 = Relation.unary("r3");
        Expression e = r1.in(r2).thenElse(r2, r1);
        Formula f = e.eq(r2).and(e.in(r3));
        Object o1 = "o1";
        Object o2 = "o2";
        Universe univ = new Universe(Arrays.asList(o1, o2));
        TupleFactory factory = univ.factory();
        TupleSet set1 = factory.setOf(o1);
        TupleSet set2 = factory.setOf(o2);
        Bounds bounds = new Bounds(univ);
        bounds.bound(r1, set1);
        bounds.boundExactly(r2, set2);
        bounds.bound(r3, set1);

        assertEquals(Solution.Outcome.TRIVIALLY_UNSATISFIABLE, solver.solve(f, bounds).outcome());

    }

    public final void testVincent_02182006() {
        // set ups universe of atoms [1..257]
        final List<Integer> atoms = new ArrayList<Integer>();

        // change this to 256, and the program works
        for (int i = 0; i < 257; i++) {
            atoms.add(i + 1);
        }

        final Universe universe = new Universe(atoms);
        final Bounds bounds = new Bounds(universe);
        final TupleFactory factory = universe.factory();

        final Relation oneRel = Relation.unary("oneRel");
        final Relation pCourses = Relation.binary("pCourses");
        final Relation prev = Relation.binary("prev");
        final Relation sCourses = Relation.binary("sCourses");
        final Relation prereqs = Relation.binary("prereqs");
        final Relation semester = Relation.unary("Semester");
        final Relation course = Relation.unary("Course");
        final Relation prereqset = Relation.unary("PrereqSet");

        final int courseIndex = 0;
        final int courseScope = 254;
        final int semesterIndex = 254;
        final int semesterScope = 2;
        final int prereqsetIndex = 256;
        final int prereqsetScope = 1;

        bounds.bound(course, factory.range(factory.tuple(atoms.get(courseIndex)), factory.tuple(atoms.get(courseIndex + courseScope - 1))));
        bounds.bound(semester, factory.range(factory.tuple(atoms.get(semesterIndex)), factory.tuple(atoms.get(semesterIndex + semesterScope - 1))));
        bounds.bound(prereqset, factory.range(factory.tuple(atoms.get(prereqsetIndex)), factory.tuple(atoms.get(prereqsetIndex + prereqsetScope - 1))));

        bounds.bound(oneRel, factory.setOf(factory.tuple(atoms.get(0))), factory.setOf(factory.tuple(atoms.get(0))));

        // list1 = [256, 2]
        // list2 = [256, 3]
        // pCoursesTS = [ [256, 2], [256, 3] ]
        List<Integer> list1 = new ArrayList<Integer>();
        list1.add(atoms.get(256));
        list1.add(atoms.get(1));
        List<Integer> list2 = new ArrayList<Integer>();
        list2.add(atoms.get(256));
        list2.add(atoms.get(2));
        TupleSet pCoursesTS = factory.setOf(factory.tuple(list1), factory.tuple(list2));
        bounds.bound(pCourses, pCoursesTS, pCoursesTS);

        // prevTS = [ [255, 254] ]
        TupleSet prevTS = factory.setOf(factory.tuple((Object) atoms.get(255), (Object) atoms.get(254)));
        bounds.bound(prev, prevTS, prevTS);

        // sCourses can be anything from Semester -> Course
        bounds.bound(sCourses, factory.area(factory.tuple((Object) atoms.get(semesterIndex), (Object) atoms.get(courseIndex)),

                                            factory.tuple((Object) atoms.get(semesterIndex + semesterScope - 1), (Object) atoms.get(courseIndex + courseScope - 1))));

        // pCoursesTS = [ [0, 256] ]
        TupleSet prereqsTS = factory.setOf(factory.tuple((Object) atoms.get(0), (Object) atoms.get(256)));
        bounds.bound(prereqs, prereqsTS, prereqsTS);

        // all s: futureSemesters | all c: s.courses | no c.prereqs or some p:
        // c.prereqs | p.courses in s.prev^.courses
        final Variable s = Variable.unary("s"), c = Variable.unary("c"), p = Variable.unary("p");
        Formula formula = (p.join(pCourses).in(s.join(prev.closure()).join(sCourses)).forAll(p.oneOf(c.join(prereqs)))).forAll(c.oneOf(s.join(sCourses))).forAll(s.oneOf(semester));

        // System.out.println(formula);

        final Instance instance = solver.solve(formula, bounds).instance();
        assertNotNull(instance);
    }

    public final void testVincent_02172006() {
        // set ups universe of atoms [1..257]
        final List<Integer> atoms = new ArrayList<Integer>();

        // change this to 256, and the program works
        for (int i = 0; i < 257; i++) {
            atoms.add(i + 1);
        }

        final Universe universe = new Universe(atoms);
        final Bounds bounds = new Bounds(universe);
        final TupleFactory factory = universe.factory();

        final Relation oneRel = Relation.unary("oneRel");
        final Relation pCourses = Relation.binary("pCourses");
        final Relation prev = Relation.binary("prev");
        final Relation sCourses = Relation.binary("sCourses");
        final Relation prereqs = Relation.binary("prereqs");
        final Relation rel = Relation.unary("rel");

        bounds.bound(oneRel, factory.setOf(factory.tuple(atoms.get(0))), factory.setOf(factory.tuple(atoms.get(0))));
        bounds.bound(rel, factory.allOf(1));

        // list1 and list2 are temp lists for creating bounds for binary
        // relations below
        // list1 = [1, 2]
        // list2 = [3, 2]
        // ts = [ [1, 2], [2, 2], [3, 2] ]
        List<Integer> list1 = new ArrayList<Integer>();
        list1.add(atoms.get(0));
        list1.add(atoms.get(1));
        List<Integer> list2 = new ArrayList<Integer>();
        list2.add(atoms.get(2));
        list2.add(atoms.get(1));
        TupleSet ts = factory.area(factory.tuple(list1), factory.tuple(list2));

        bounds.bound(pCourses, ts);
        bounds.bound(prev, ts);
        bounds.bound(sCourses, ts);
        bounds.bound(prereqs, ts);

        // all s: futureSemesters | all c: s.courses | no c.prereqs or some p:
        // c.prereqs | p.courses in s.prev^.courses
        final Variable s = Variable.unary("s"), c = Variable.unary("c"), p = Variable.unary("p");
        Formula formula = (p.join(pCourses).in(s.join(prev.closure()).join(sCourses)).forAll(p.oneOf(c.join(prereqs)))).forAll(c.oneOf(s.join(sCourses))).forAll(s.oneOf(rel));

        // System.out.println(formula);
        // solve

        final Instance instance = solver.solve(formula, bounds).instance();
        assertNotNull(instance);

    }

    public final void testEmina_02162006() {
        final IntTreeSet s = new IntTreeSet();
        for (int i = 0; i < 5; i++) {
            s.add(i);
        }
        final IntTreeSet s1 = new IntTreeSet();
        s1.add(0);

        final IntSet intersection = new IntTreeSet(s);
        intersection.retainAll(s1);
        s.removeAll(intersection);

        assertSameContents(s, 1, 2, 3, 4);
        assertSameContents(s1, 0);
        assertSameContents(intersection, 0);
    }

    public final void testVincent_02162006() {
        // set ups universe of atoms [1..257]
        final List<Integer> atoms = new ArrayList<Integer>();

        // change this to 256, and the program works
        for (int i = 0; i < 257; i++) {
            atoms.add(i + 1);
        }

        final Universe universe = new Universe(atoms);
        final Bounds bounds = new Bounds(universe);
        final TupleFactory factory = universe.factory();

        // oneRel is bounded to the Integer 1
        final Relation oneRel = Relation.unary("oneRel");

        // rel can contain anything
        final Relation rel = Relation.unary("rel");

        bounds.bound(oneRel, factory.setOf(factory.tuple(atoms.get(0))), factory.setOf(factory.tuple(atoms.get(0))));
        bounds.bound(rel, factory.allOf(1));

        // constraint: oneRel in rel
        Formula formula = oneRel.in(rel);

        // solve

        final Instance instance = solver.solve(formula, bounds).instance();
        assertNotNull(instance);
        // System.out.println(instance);

    }

    private final void assertSameContents(IntSet s, int... elts) {
        assertEquals(elts.length, s.size());
        for (int i : elts)
            assertTrue(s.contains(i));
    }

    public final void testVincent_02132006() {
        IntTreeSet set = new IntTreeSet();
        for (int i = 0; i < 2; i++) {
            set.add(i);
        }

        IntTreeSet set2 = new IntTreeSet();
        for (int i = 0; i < 2; i++) {
            set2.add(i);
        }

        set.removeAll(set2);
        IntIterator setIterator = set.iterator();
        assertFalse(setIterator.hasNext());
        assertFalse(setIterator.hasNext());

        set.addAll(set2);
        assertSameContents(set, 0, 1);

        set2.clear();
        for (int i = 3; i < 5; i++) {
            set2.add(i);
        }

        set.addAll(set2);
        assertSameContents(set, 0, 1, 3, 4);

        set2.clear();
        for (int i = 1; i < 4; i++) {
            set2.add(i);
        }

        set.addAll(set2);
        assertSameContents(set, 0, 1, 2, 3, 4);
    }

    public final void testEmina_01232006() {
        final List<String> atoms = new ArrayList<String>(5);
        for (int i = 0; i < 5; i++)
            atoms.add("a" + i);
        final Universe u = new Universe(atoms);
        final TupleFactory tf = u.factory();

        final Relation r1 = Relation.unary("r1"), r2 = Relation.binary("r2"), r3 = Relation.ternary("r3");
        final Bounds b = new Bounds(u);
        final TupleSet r2Bound = tf.noneOf(2);
        for (int i = 0; i < 4; i++)
            r2Bound.add(tf.tuple(atoms.get(i), atoms.get(i)));
        r2Bound.add(tf.tuple("a4", "a1"));
        r2Bound.add(tf.tuple("a4", "a2"));
        b.bound(r2, r2Bound);
        b.bound(r1, tf.setOf("a0", "a3"), tf.setOf("a0", "a3", "a4"));
        b.bound(r3, tf.setOf(tf.tuple("a0", "a0", "a0"), tf.tuple("a3", "a3", "a3")));
        final Formula f = r1.product(r2).in(r3);

        final Instance instance = solver.solve(f, b).instance();
        assertTrue((new Evaluator(instance)).evaluate(f));
        // System.out.println(instance);
        // System.out.println((new Evaluator(instance)).evaluate(f ));

    }

    public final void testEmina_01192006() {
        IntBitSet s = new IntBitSet(64);
        for (int i = 4; i < 8; i++) {
            for (int j = 0; j < 4; j++) {
                s.add(i * 8 + j);
            }
        }
        // System.out.println(s);
        for (int i = 4; i < 8; i++) {
            assertTrue(s.iterator(i * 8, (i + 1) * 8 - 1).hasNext());
            int count = 0;
            for (IntIterator iter = s.iterator(i * 8, (i + 1) * 8 - 1); iter.hasNext();) {
                count += iter.next() % 8;
            }
            assertEquals(count, 6);
        }
        for (int i = 4; i < 8; i++) {
            assertTrue(s.iterator((i + 1) * 8 - 1, i * 8).hasNext());
            int count = 0;
            for (IntIterator iter = s.iterator((i + 1) * 8 - 1, i * 8); iter.hasNext();) {
                count += iter.next() % 8;
            }
            assertEquals(count, 6);
        }
    }

    public final void testGreg_01192006() {
        // circular linked list
        Relation Entry = Relation.unary("Entry");
        Relation head = Relation.unary("head");
        Relation next = Relation.binary("next");
        Formula nextFun = next.function(Entry, Entry);

        // bijection between indices and entries in linked list
        Relation Index = Relation.unary("Index");
        Relation index2Entry = Relation.binary("index2Entry");
        Expression entries = head.join(next.closure());
        Variable e = Variable.unary("e");
        Expression preImage = index2Entry.join(e);
        Formula index2EntryBij = e.in(entries).implies(preImage.one()).and(e.in(entries).not().implies(preImage.no())).forAll(e.oneOf(Entry));

        // try to force list to have three distinct entries
        Variable e1 = Variable.unary("e1");
        Variable e2 = Variable.unary("e2");
        Variable e3 = Variable.unary("e3");
        Formula threeEntries = e1.eq(e2).not().and(e1.eq(e3).not()).and(e2.eq(e3).not()).forSome(e1.oneOf(entries).and(e2.oneOf(entries).and(e3.oneOf(entries))));
        Formula simulate = head.one().and(nextFun).and(index2EntryBij).and(threeEntries);

        Object Entry0 = "Entry0";
        Object Entry1 = "Entry1";
        Object Entry2 = "Entry2";
        Object Entry3 = "Entry3";
        Object Index0 = "Index0";
        Object Index1 = "Index1";
        Object Index2 = "Index2";
        Object Index3 = "Index3";

        Universe univ = new Universe(Arrays.asList(Entry0, Entry1, Entry2, Entry3, Index0, Index1, Index2, Index3));
        TupleFactory factory = univ.factory();
        TupleSet entryTuples = factory.setOf(Entry0, Entry1, Entry2, Entry3);
        TupleSet indexTuples = factory.setOf(Index0, Index1, Index2, Index3);

        Instance instance = new Instance(univ);
        instance.add(Entry, entryTuples);
        instance.add(head, factory.setOf(Entry0));
        instance.add(Index, indexTuples);

        Tuple next0 = factory.tuple(Entry0, Entry1);
        Tuple next1 = factory.tuple(Entry1, Entry2);
        Tuple next2 = factory.tuple(Entry2, Entry3);
        Tuple next3 = factory.tuple(Entry3, Entry0);
        instance.add(next, factory.setOf(next0, next1, next2, next3));

        Tuple i2e0 = factory.tuple(Index0, Entry0);
        Tuple i2e1 = factory.tuple(Index1, Entry1);
        Tuple i2e2 = factory.tuple(Index2, Entry2);
        Tuple i2e3 = factory.tuple(Index3, Entry3);
        instance.add(index2Entry, factory.setOf(i2e0, i2e1, i2e2, i2e3));

        Evaluator eval = new Evaluator(instance);
        assertTrue(eval.evaluate(simulate));

        Bounds bounds = new Bounds(univ);
        bounds.boundExactly(Entry, entryTuples);
        bounds.bound(head, entryTuples);
        bounds.bound(next, entryTuples.product(entryTuples));
        bounds.bound(Index, indexTuples);
        bounds.bound(index2Entry, indexTuples.product(entryTuples));
        // Solver solver = new Solver(SATSolverName.Default);

        // System.out.println(simulate);
        // System.out.println(bounds);
        // System.out.println(instance);
        instance = solver.solve(simulate, bounds).instance();
        // System.out.println(instance);
        assertNotNull(instance);

    }

    public final void testMana_01132006() {
        // r0=[[], [[null], [DblLinkedList0]]],
        // null=[[[null]], [[null]]],
        // head=[[], [[DblLinkedList0, null], [DblLinkedList0,
        // DblLinkedListElem0]]],
        // next=[[], [[DblLinkedListElem0, null], [DblLinkedListElem0,
        // DblLinkedListElem0]]],
        // univ=[[[null], [DblLinkedList0], [1], [DblLinkedListElem0], [0]],
        // [[null], [DblLinkedList0], [1], [DblLinkedListElem0], [0]]]
        // r1=[[], [[null], [DblLinkedListElem0]]],
        final List<String> atoms = new ArrayList<String>(5);
        atoms.add("null");
        atoms.add("DblLinkedList0");
        atoms.add("1");
        atoms.add("DblLinkedListElem0");
        atoms.add("0");
        final Universe u = new Universe(atoms);
        final TupleFactory t = u.factory();

        // !((head . univ) in ((if (r1 in null) then (head ++ (r0 -> (r1 .
        // next))) else head) . univ))

        final Relation head = Relation.binary("head"), univ = Relation.unary("univ"), r0 = Relation.unary("r0"),
                        r1 = Relation.unary("r1"), next = Relation.binary("next"), nil = Relation.unary("null"),
                        none = Relation.unary("none");

        final Expression override = head.override(r0.product(r1.join(next)));
        final Expression ifElse = r1.in(nil).thenElse(override, head);
        final Formula f = head.join(univ).in(ifElse.join(univ)).not();

        final Bounds b = new Bounds(u);
        b.bound(r0, t.setOf("null", "DblLinkedList0"));
        b.bound(r1, t.setOf("null", "DblLinkedListElem0"));
        b.bound(head, t.setOf("DblLinkedList0").product(b.upperBound(r1)));

        b.bound(next, t.setOf(t.tuple("DblLinkedListElem0", "null"), t.tuple("DblLinkedListElem0", "DblLinkedListElem0")));
        b.boundExactly(univ, t.allOf(1));
        b.boundExactly(nil, t.setOf("null"));
        b.boundExactly(none, t.noneOf(1));

        // System.out.println(f);
        // System.out.println(b);

        final Instance instance = solver.solve(f, b).instance();
        assertNull(instance);

    }

    public final void testGreg_11232005() {
        final List<String> atoms = new ArrayList<String>(3);
        atoms.add("-1");
        atoms.add("0");
        atoms.add("1");
        final Universe u = new Universe(atoms);
        final TupleFactory t = u.factory();

        final Relation inc = Relation.binary("inc"), add = Relation.ternary("add"), one = Relation.unary("1"),
                        param0 = Relation.unary("param0"), ints = Relation.unary("int");

        // (one param0 && ((1 . (param0 . add)) in (param0 . ^inc)))
        final Formula f = param0.one().and((one.join(param0.join(add))).in(param0.join(inc.closure())));

        final Bounds b = new Bounds(u);

        b.bound(param0, t.allOf(1));
        b.boundExactly(one, t.setOf(t.tuple("1")));
        b.boundExactly(ints, t.allOf(1));
        b.boundExactly(inc, t.setOf(t.tuple("-1", "0"), t.tuple("0", "1")));
        // [1, 1, -1], [1, -1, 0], [1, 0, 1], [-1, 1, 0], [-1, -1, 1],
        // [-1, 0, -1], [0, 1, 1], [0, -1, -1], [0, 0, 0]]
        b.boundExactly(add, t.setOf(t.tuple("1", "1", "-1"), t.tuple("1", "-1", "0"), t.tuple("1", "0", "1"), t.tuple("-1", "1", "0"), t.tuple("-1", "-1", "1"), t.tuple("-1", "0", "-1"), t.tuple("0", "1", "1"), t.tuple("0", "-1", "-1"), t.tuple("0", "0", "0")));

        // System.out.println(f);
        // System.out.println(b);

        final Instance instance = solver.solve(f, b).instance();
        assertTrue((new Evaluator(instance)).evaluate(f));
        // System.out.println(instance);
        // System.out.println((new Evaluator(instance)).evaluate(f ));

    }

    public final void testGreg_01052006() {

        // final TreeSequence<Integer> t = new TreeSequence<Integer>();
        // final int[] elts = {107, 31, 86, 72, 6, 119, 23, 131};
        // for(int i = 0; i < elts.length; i++) {
        // t.put(elts[i], 0);
        // }
        // final int[] sorted = new int[elts.length];
        // System.arraycopy(elts, 0, sorted, 0, elts.length);
        // Arrays.sort(sorted);
        // int count = 0;
        // for(IndexedEntry<Integer> e : t) {
        // assertEquals(sorted[count++], e.index());
        // }
        // t.remove(72);
        // t.put(72,0);
        // count = 0;
        // for(IndexedEntry<Integer> e : t) {
        // assertEquals(sorted[count++], e.index());
        // }

        final List<Object> atoms = new ArrayList<Object>(12);
        atoms.add(2);
        atoms.add(4);
        atoms.add(-2);
        atoms.add("null");
        atoms.add("array0");
        atoms.add(6);
        atoms.add(1);
        atoms.add(-1);
        atoms.add(-3);
        atoms.add(3);
        atoms.add(5);
        atoms.add(0);

        final Universe u = new Universe(atoms);
        final TupleFactory f = u.factory();

        final TupleSet tdiv = f.noneOf(3);

        for (int i = -3; i <= 6; i++) {
            for (int j = -3; j <= 6; j++) {
                if (j != 0) {
                    int divij = i / j;
                    if (-3 <= divij && divij <= 6)
                        tdiv.add(f.tuple(i, j, divij));
                    else
                        tdiv.add(f.tuple(i, j, (10 + divij) % 10));
                }
            }
        }

        final TupleSet tdivcopy = tdiv.clone();
        for (int i = -3; i <= 6; i++) {
            for (int j = -3; j <= 6; j++) {
                if (j != 0) {
                    int divij = i / j;
                    if (-3 <= divij && divij <= 6)
                        assertTrue(tdivcopy.contains(f.tuple(i, j, divij)));
                    else
                        assertTrue(tdivcopy.contains(f.tuple(i, j, (10 + divij) % 10)));
                }
            }
        }
    }

    public final void testAleks_03102013() {
        final int NUM = 100;
        // run it multiple times, because whether the bug is going to be
        // exhibited depends on the ordering of items in a set (concretely,
        // shared nodes in the AnnotatedNode class
        for (int i = 0; i < NUM; i++) {
            doTestAleks_03102013();
        }
    }

    private final void doTestAleks_03102013() {
        Relation r = Relation.unary("R");
        Relation s = Relation.binary("f");
        Variable v = Variable.unary("e");
        Decl decl = v.oneOf(r);
        Expression shared = v.join(s);
        Formula expr = (shared.difference(shared)).one().forAll(decl);

        Formula fin = expr.and(expr.not());

        List<Object> atomlist = new LinkedList<Object>();
        atomlist.add("R$0");
        atomlist.add("R$1");
        atomlist.add("R$2");

        Universe universe = new Universe(atomlist);
        TupleFactory factory = universe.factory();
        Bounds bounds = new Bounds(universe);

        bounds.bound(r, factory.allOf(1));
        bounds.bound(s, factory.allOf(2));

        Solver solver = new Solver();
        solver.options().setSolver(SATFactory.DefaultSAT4J);
        solver.options().setBitwidth(4);
        solver.options().setSkolemDepth(0);
        solver.options().setLogTranslation(0);
        Solution sol = solver.solve(fin, bounds);
        assertNull(sol.instance());
    }

}
