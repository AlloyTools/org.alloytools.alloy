/*
 * TranslatorTest.java
 * Created on Jul 6, 2005
 */
package tests.basic;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import junit.framework.TestCase;
import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.IntConstant;
import kodkod.ast.IntExpression;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.ast.operator.ExprOperator;
import kodkod.ast.operator.FormulaOperator;
import kodkod.ast.operator.IntOperator;
import kodkod.ast.operator.Multiplicity;
import kodkod.ast.operator.Quantifier;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;
import kodkod.instance.Tuple;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

/**
 * Tests {@link kodkod.engine.fol2sat.Translator FOL to SAT translation} and
 * {@link kodkod.engine.fol2sat.Sat2CnfTranslator SAT to CNF translation}.
 *
 * @author Emina Torlak
 */
public class TranslatorTest extends TestCase {

    private final TupleFactory factory;
    private final Solver       solver;
    private final Relation[]   r1, r2, r3;
    private final Tuple        t112, t212, t312;
    private final Bounds       bounds;

    public TranslatorTest(String arg0) {
        super(arg0);
        this.solver = new Solver();
        List<Integer> atoms = new ArrayList<Integer>(10);
        for (int i = 0; i < 10; i++) {
            atoms.add(i);
        }
        final Universe universe = new Universe(atoms);
        this.factory = universe.factory();
        this.t112 = factory.tuple(1, 4);
        this.t212 = factory.tuple(2, 57);
        this.t312 = factory.tuple(3, 345);
        this.r1 = new Relation[4];
        this.r2 = new Relation[4];
        this.r3 = new Relation[4];
        for (int i = 0; i < 4; i++) {

            r1[i] = Relation.unary("r1" + i);
            r2[i] = Relation.binary("r2" + i);
            r3[i] = Relation.ternary("r3" + i);

        }

        bounds = new Bounds(universe);

        bounds.bound(r1[0], factory.allOf(1));
        bounds.bound(r1[1], factory.range(factory.tuple(2), t112));
        bounds.bound(r1[2], factory.range(t112, t112));
        bounds.bound(r1[3], factory.range(factory.tuple(5), factory.tuple(8)));

        bounds.bound(r2[0], factory.allOf(2));
        bounds.bound(r2[1], factory.area(factory.tuple(2, 35), t212));
        bounds.bound(r2[2], factory.setOf(t212));
        bounds.bound(r2[3], factory.area(factory.tuple(2, 60), factory.tuple(2, 86)));

        bounds.bound(r3[0], factory.allOf(3));
        bounds.bound(r3[1], factory.area(factory.tuple(3, 123), t312));
        bounds.bound(r3[2], factory.setOf(t312));
        bounds.bound(r3[3], factory.area(factory.tuple(3, 700), factory.tuple(3, 897)));

        // System.out.println(bounds.upperBound(r3[0]).size());
        // System.out.println(bounds.upperBound(r3[1]).size());
        // System.out.println(bounds.upperBound(r3[2]).size());
        // System.out.println(bounds.upperBound(r3[3]).size());

    }

    private Instance solve(Formula formula) {

        return solver.solve(formula, bounds).instance();

    }

    private boolean isSatisfiable(Formula formula) {
        return (solve(formula) == null ? false : true);
    }

    private final void testIntersectionMultiplicity(Multiplicity mult, Relation p, Relation q, Tuple intersection) {
        final Instance m = solve(p.intersection(q).apply(mult));
        assertNotNull(m);
        final Set<Tuple> ps = m.tuples(p), qs = m.tuples(q);
        assertFalse(ps.isEmpty());
        assertFalse(qs.isEmpty());
        assertTrue(ps.contains(intersection));
        assertTrue(qs.contains(intersection));
    }

    private final void testTranslateNonEmptyMultiplicity(Multiplicity mult) {

        testTranslateMultiplicity(mult, true, false);
        testIntersectionMultiplicity(mult, r1[1], r1[2], t112);
        testIntersectionMultiplicity(mult, r2[1], r2[2], t212);
        testIntersectionMultiplicity(mult, r3[1], r3[2], t312);
    }

    private final void testTranslateMultiplicity(Multiplicity mult, boolean trueTest, boolean falseTest) {
        for (int i = 0; i < 4; i++) {
            assertTrue(isSatisfiable(r1[i].apply(mult)));
            assertTrue(isSatisfiable(r2[i].apply(mult)));
            // assertTrue(solve(r3[i].apply(mult)));
        }

        // mult rx1 & rx3
        assertEquals(falseTest, isSatisfiable(r1[1].intersection(r1[3]).apply(mult)));
        assertEquals(falseTest, isSatisfiable(r2[1].intersection(r2[3]).apply(mult)));
        assertEquals(falseTest, isSatisfiable(r3[1].intersection(r3[3]).apply(mult)));

        // mult rx3 - rx3
        assertEquals(falseTest, isSatisfiable(r1[3].difference(r1[3]).apply(mult)));
        assertEquals(falseTest, isSatisfiable(r2[3].difference(r2[3]).apply(mult)));
        assertEquals(falseTest, isSatisfiable(r3[3].difference(r3[3]).apply(mult)));

        // mult r11->r13 & r21
        assertEquals(trueTest, isSatisfiable(r1[1].product(r1[3]).intersection(r2[1]).apply(mult)));
        // mult r11->r21 & r31
        assertEquals(trueTest, isSatisfiable(r1[1].product(r2[1]).intersection(r3[1]).apply(mult)));

        // mult rx1 + rx3
        assertEquals(trueTest, isSatisfiable(r1[1].union(r1[3]).apply(mult)));
        assertEquals(trueTest, isSatisfiable(r2[1].union(r2[3]).apply(mult)));
        assertEquals(trueTest, isSatisfiable(r3[1].union(r3[3]).apply(mult)));

        // mult r21.r13
        assertEquals(trueTest, isSatisfiable(r2[1].join(r1[3]).apply(mult)));
        // mult r31.r21
        assertEquals(trueTest, isSatisfiable(r3[1].join(r2[1]).apply(mult)));

        // mult ^r21
        assertEquals(trueTest, isSatisfiable(r2[1].closure().apply(mult)));
        // mult ~r23
        assertEquals(trueTest, isSatisfiable(r2[3].transpose().apply(mult)));
    }

    public final void testTranslateMultiplicityFormula_NO() {
        testTranslateMultiplicity(Multiplicity.NO, true, true);
    }

    public final void testTranslateMultiplicityFormula_LONE() {
        // testTranslateMultiplicity(MultiplicityFormula.Multiplicity.LONE,
        // true, true);
        assertEquals(true, isSatisfiable(r3[1].union(r3[3]).apply(Multiplicity.LONE)));
        // assertEquals(true,
        // isSatisfiable(r3[3].difference(r3[1]).apply(MultiplicityFormula.Multiplicity.LONE)));
    }

    public final void testTranslateMultiplicityFormula_ONE() {
        testTranslateNonEmptyMultiplicity(Multiplicity.ONE);
    }

    public final void testTranslateMultiplicityFormula_SOME() {
        testTranslateNonEmptyMultiplicity(Multiplicity.SOME);
    }

    public final void testTranslateComparisonFormula() {
        for (int i = 0; i < 4; i++) {
            assertTrue(isSatisfiable(r1[i].in(r1[i])));
            assertTrue(isSatisfiable(r2[i].in(r2[i])));
            assertTrue(isSatisfiable(r3[i].in(r3[i])));
        }

        // some rx2 && (rx1 & rx2 in rx2)
        assertTrue(isSatisfiable(r1[2].some().and(r1[1].intersection(r1[2]).in(r1[2]))));
        assertTrue(isSatisfiable(r2[2].some().and(r2[1].intersection(r2[2]).in(r2[2]))));
        assertTrue(isSatisfiable(r3[2].some().and(r3[1].intersection(r3[2]).in(r3[2]))));

        // one rx2 && (rx1 & rx2 = rx2)
        assertTrue(isSatisfiable(r1[2].one().and(r1[1].intersection(r1[2]).eq(r1[2]))));
        assertTrue(isSatisfiable(r2[2].one().and(r2[1].intersection(r2[2]).eq(r2[2]))));
        assertTrue(isSatisfiable(r3[2].one().and(r3[1].intersection(r3[2]).eq(r3[2]))));

        // !(rx3 in rx0)
        assertTrue(isSatisfiable(r1[3].in(r1[0]).not()));
        assertTrue(isSatisfiable(r2[3].in(r2[0]).not()));
        assertTrue(isSatisfiable(r3[3].in(r3[0]).not()));

        // some rx0 && (rx1 + rx2 + rx3 in rx0)
        assertTrue(isSatisfiable(r1[0].some().and(r1[1].union(r1[2]).union(r1[3]).in(r1[0]))));
        assertTrue(isSatisfiable(r2[0].some().and(r2[1].union(r2[2]).union(r2[3]).in(r2[0]))));
        assertTrue(isSatisfiable(r3[0].some().and(r3[1].union(r3[2]).union(r3[3]).in(r3[0]))));

        // System.out.println("-----------------");
        // System.out.println(bounds.upperBound(r1[1]));
        // System.out.println(bounds.upperBound(r1[3]));
        // System.out.println(bounds.upperBound(r2[1]));
        // some r11 && some r13 && r11->r13 = r21
        assertTrue(isSatisfiable(r1[1].some().and(r1[3].some()).and(r1[1].product(r1[3]).eq(r2[1]))));

        // r21.r13 in r11
        assertTrue(isSatisfiable(r2[1].join(r1[3]).in(r1[1])));

        // *r22 in r21 + iden
        assertTrue(isSatisfiable(r2[2].reflexiveClosure().in(r2[1].union(Expression.IDEN))));
    }

    private final void testTranslateQuantifiedFormula(Quantifier quant) {
        // quant v1: r1[i] | v1 in rx0
        final Variable v1 = Variable.unary("v1"), v2 = Variable.unary("v2");
        for (int i = 1; i < 4; i++) {
            assertTrue(isSatisfiable(v1.in(r1[0]).quantify(quant, v1.oneOf(r1[i]))));
        }

        // quant v1 : r1[2], v2: r1[3] | v1->v2 in r2[1]
        assertTrue(isSatisfiable(v1.product(v2).in(r2[1]).quantify(quant, v1.oneOf(r1[2]).and(v2.oneOf(r1[3])))));

        // quant v1 : r1[3] | some r3[3].v1 & r2[3]
        assertTrue(isSatisfiable(r3[3].join(v1).intersection(r2[3]).some().quantify(quant, v1.oneOf(r1[3]))));

        // quant v1 : r1[3] | some v1.(~r2[1])
        assertTrue(isSatisfiable(v1.join(r2[1].transpose()).some().quantify(quant, v1.oneOf(r1[3]))));
        // quant v1: r1[3] | some v1.(^r2[3])
        assertTrue(isSatisfiable(v1.join(r2[3].closure()).some().quantify(quant, v1.oneOf(r1[3]))));

    }

    public final void testTranslateQuantifiedFormula_ALL() {
        testTranslateQuantifiedFormula(Quantifier.ALL);
    }

    public final void testTranslateQuantifiedFormula_SOME() {
        testTranslateQuantifiedFormula(Quantifier.SOME);
    }

    public final void testTranslateComprehension() {
        final Variable v1 = Variable.unary("v1"), v2 = Variable.unary("v2");

        // some { v1: r11 + r12 | some v1.r21 }
        assertTrue(isSatisfiable((v1.join(r2[1]).some()).comprehension(v1.oneOf(r1[1].union(r1[2]))).some()));

        // one { v1: r13, v2: r12 | v1->v2 in r23 }
        assertTrue(isSatisfiable((v1.product(v2).in(r2[3]).comprehension(v1.oneOf(r1[3]).and(v2.oneOf(r1[2])))).one()));

        // one { v1: r13, v2: r12 | v2->v1 in ~r23 }
        assertTrue(isSatisfiable((v2.product(v1).in(r2[3].transpose()).comprehension(v1.oneOf(r1[3]).and(v2.oneOf(r1[2])))).one()));

    }

    public final void testTranslateProjection() {

        assertTrue(isSatisfiable(r3[0].eq(r2[0].project(IntConstant.constant(0), IntConstant.constant(1), IntConstant.constant(0)))));

        assertTrue(isSatisfiable(r2[1].in(r3[0].project(r1[3].count(), r1[2].count()))));

        final Variable v = Variable.nary("r", 2);
        assertFalse(isSatisfiable(v.transpose().eq(v.project(IntConstant.constant(1), IntConstant.constant(0))).not().forSome(v.setOf(r2[0]))));

        bounds.boundExactly(r3[0], bounds.upperBound(r3[0]));
        bounds.boundExactly(r2[0], bounds.upperBound(r2[0]));

        assertTrue(isSatisfiable(r3[0].project(IntConstant.constant(0), IntConstant.constant(1)).eq(r2[0])));
        assertTrue(isSatisfiable(r3[0].project(IntConstant.constant(0), IntConstant.constant(4), IntConstant.constant(2)).eq(Expression.NONE.product(Expression.NONE).product(Expression.NONE))));
        assertTrue(isSatisfiable(r3[0].project(IntConstant.constant(0), IntConstant.constant(-1), IntConstant.constant(2)).eq(Expression.NONE.product(Expression.NONE).product(Expression.NONE))));

    }

    public final void testIFF() {
        // some r11 && (r11 in r12 iff r12 in r11)
        Formula f = r1[1].some().and(r1[1].in(r1[2]).iff(r1[2].in(r1[1])));
        assertTrue(isSatisfiable(f));
        // some r11 && no r12 && (r11 in r12 iff r12 in r11)
        assertFalse(isSatisfiable(f.and(r1[2].no())));
    }

    public final void testFlattening() {
        final List<String> atoms = new ArrayList<String>(9);
        atoms.add("-1");
        atoms.add("0");
        atoms.add("1");
        atoms.add("null");
        for (int i = 0; i < 5; i++) {
            atoms.add("m" + i);
        }
        final Universe u = new Universe(atoms);
        final TupleFactory t = u.factory();

        final Relation[] m = new Relation[5];
        for (int i = 0; i < 5; i++) {
            m[i] = Relation.unary("m" + i);
        }

        final Relation univ = Relation.unary("univ"), none = Relation.unary("none"), iden = Relation.binary("inden"),
                        mutant = Relation.unary("mutant"), inc = Relation.binary("inc"), add = Relation.ternary("add"),
                        i0 = Relation.unary("i0"), zero = Relation.unary("0"), one = Relation.unary("1"),
                        ints = Relation.unary("int");

        final Bounds b = new Bounds(u);

        b.boundExactly(univ, t.allOf(1));
        b.boundExactly(none, t.noneOf(1));
        TupleSet idenSet = t.noneOf(2);
        for (String atom : atoms) {
            idenSet.add(t.tuple(atom, atom));
        }
        b.boundExactly(iden, idenSet);

        b.bound(mutant, t.range(t.tuple("m0"), t.tuple("m4")));
        for (int i = 0; i < 5; i++) {
            b.boundExactly(m[i], t.setOf("m" + i));
        }

        b.bound(i0, t.range(t.tuple("-1"), t.tuple("1")));
        b.boundExactly(zero, t.setOf(t.tuple("0")));
        b.boundExactly(one, t.setOf(t.tuple("1")));
        b.boundExactly(ints, t.allOf(1));
        b.boundExactly(inc, t.setOf(t.tuple("-1", "0"), t.tuple("0", "1")));

        // [1, 1, -1], [1, -1, 0], [1, 0, 1], [-1, 1, 0], [-1, -1, 1],
        // [-1, 0, -1], [0, 1, 1], [0, -1, -1], [0, 0, 0]]
        b.boundExactly(add, t.setOf(t.tuple("1", "1", "-1"), t.tuple("1", "-1", "0"), t.tuple("1", "0", "1"), t.tuple("-1", "1", "0"), t.tuple("-1", "-1", "1"), t.tuple("-1", "0", "-1"), t.tuple("0", "1", "1"), t.tuple("0", "-1", "-1"), t.tuple("0", "0", "0")));

        /*
         * ((one i0 && one mutant) && !((if (i0 in (0 . ^~inc)) then ((add . 0) . i0)
         * else i0) = (if !((if (mutant in m4) then (if (i0 in 0) then 1 else 0) else
         * (if (mutant in m3) then (if ((i0 = 0) || (i0 in (0 . ^~inc))) then 1 else 0)
         * else (if (mutant in m2) then (if (i0 in (0 . ^inc)) then 1 else 0) else (if
         * (mutant in m1) then (if ((i0 = 0) || (i0 in (0 . ^inc))) then 1 else 0) else
         * (if (mutant in m0) then (if !(i0 in 0) then 1 else 0) else (if (i0 in (0 .
         * ^~inc)) then 1 else 0)))))) in 0) then ((add . 0) . i0) else i0)))
         */

        final Formula[] cm = new Formula[5];
        for (int i = 0; i < 5; i++) {
            cm[i] = mutant.in(m[i]);
        }

        // (i0 in (0 . ^~inc))
        final Formula fs0 = i0.in(zero.join(inc.transpose().closure()));
        // (i0 in (0 . ^inc))
        final Formula fs1 = i0.in(zero.join(inc.closure()));
        // (i0 = 0)
        final Formula fs2 = i0.eq(zero);

        final Expression em0 = cm[0].thenElse(i0.in(zero).not().thenElse(one, zero), fs0.thenElse(one, zero));
        final Expression em1 = cm[1].thenElse((fs2.or(fs1)).thenElse(one, zero), em0);
        final Expression em2 = cm[2].thenElse(fs1.thenElse(one, zero), em1);
        final Expression em3 = cm[3].thenElse(fs2.or(fs0).thenElse(one, zero), em2);
        final Expression em4 = cm[4].thenElse(i0.in(zero).thenElse(one, zero), em3);

        final Expression es1 = add.join(zero).join(i0);
        final Expression expr2 = em4.in(zero).not().thenElse(es1, i0);
        final Expression expr1 = fs0.thenElse(es1, i0);

        final Formula f = i0.one().and(mutant.one()).and(expr1.eq(expr2).not());

        final Instance instance = solver.solve(f, b).instance();
        assertNotNull(instance);

        // System.out.println(instance);

    }

    private final void testNary(ExprOperator op) {
        bounds.bound(r1[0], factory.range(factory.tuple(1, 0), factory.tuple(1, 3)));
        bounds.bound(r1[1], factory.range(factory.tuple(1, 2), factory.tuple(1, 5)));
        bounds.bound(r1[3], factory.range(factory.tuple(1, 3), factory.tuple(1, 6)));

        for (int i = 2; i <= 5; i++) {
            final Expression[] exprs = new Expression[i];
            exprs[0] = r1[0];
            Expression binExpr = r1[0];
            for (int j = 1; j < i; j++) {
                binExpr = binExpr.compose(op, r1[j % 4]);
                exprs[j] = r1[j % 4];
            }
            Expression nExpr = Expression.compose(op, exprs);
            final Solution sol = solver.solve(binExpr.eq(nExpr).not(), bounds);
            assertNull(sol.instance());
        }

    }

    public final void testNaryUnion() {
        testNary(ExprOperator.UNION);
    }

    public final void testNaryIntersection() {
        testNary(ExprOperator.INTERSECTION);
    }

    public final void testNaryProduct() {
        testNary(ExprOperator.PRODUCT);
    }

    public final void testNaryOverride() {
        testNary(ExprOperator.OVERRIDE);
    }

    private final void testNary(IntOperator op) {
        bounds.bound(r1[0], factory.range(factory.tuple(1, 0), factory.tuple(1, 3)));
        bounds.bound(r1[1], factory.range(factory.tuple(1, 2), factory.tuple(1, 5)));
        bounds.bound(r1[3], factory.range(factory.tuple(1, 3), factory.tuple(1, 6)));

        for (int i = 2; i <= 5; i++) {
            final IntExpression[] exprs = new IntExpression[i];
            exprs[0] = r1[0].count();
            IntExpression binExpr = r1[0].count();
            for (int j = 1; j < i; j++) {
                binExpr = binExpr.compose(op, r1[j % 4].count());
                exprs[j] = r1[j % 4].count();
            }
            IntExpression nExpr = IntExpression.compose(op, exprs);
            final Solution sol = solver.solve(binExpr.eq(nExpr).not(), bounds);
            assertNull(sol.instance());
        }

    }

    public final void testNaryPlus() {
        testNary(IntOperator.PLUS);
    }

    public final void testNaryMultiply() {
        testNary(IntOperator.MULTIPLY);
    }

    public final void testNaryBitwiseAnd() {
        testNary(IntOperator.AND);
    }

    public final void testNaryBitwiseOr() {
        testNary(IntOperator.OR);
    }

    private final void testNary(FormulaOperator op) {
        bounds.bound(r1[0], factory.range(factory.tuple(1, 0), factory.tuple(1, 3)));
        bounds.bound(r1[1], factory.range(factory.tuple(1, 2), factory.tuple(1, 5)));
        bounds.bound(r1[3], factory.range(factory.tuple(1, 3), factory.tuple(1, 6)));

        for (int i = 2; i <= 5; i++) {
            final Formula[] exprs = new Formula[i];
            exprs[0] = r1[0].some();
            Formula binExpr = r1[0].some();
            for (int j = 1; j < i; j++) {
                binExpr = binExpr.compose(op, r1[j % 4].some());
                exprs[j] = r1[j % 4].some();
            }
            Formula nExpr = Formula.compose(op, exprs);
            final Solution sol = solver.solve(binExpr.iff(nExpr).not(), bounds);
            assertNull(sol.instance());
        }

    }

    public final void testNaryAnd() {
        testNary(FormulaOperator.AND);
    }

    public final void testNaryOr() {
        testNary(FormulaOperator.OR);
    }

}
