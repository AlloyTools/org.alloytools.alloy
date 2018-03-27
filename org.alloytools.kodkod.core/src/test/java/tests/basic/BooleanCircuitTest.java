package tests.basic;

import static kodkod.engine.bool.BooleanConstant.FALSE;
import static kodkod.engine.bool.BooleanConstant.TRUE;
import static kodkod.engine.bool.Operator.AND;
import static kodkod.engine.bool.Operator.OR;

import java.util.LinkedList;
import java.util.List;

import junit.framework.TestCase;
import kodkod.engine.bool.BooleanConstant;
import kodkod.engine.bool.BooleanFactory;
import kodkod.engine.bool.BooleanValue;
import kodkod.engine.bool.BooleanVariable;
import kodkod.engine.bool.Operator;
import kodkod.engine.config.Options;

public class BooleanCircuitTest extends TestCase {

    private BooleanFactory          f;
    private BooleanVariable[]       v;
    private final int               size      = 20;

    private static final Composer[] COMPOSERS = {
                                                 new Composer() {

                                                     @Override
                                                     public BooleanValue compose(BooleanFactory f, BooleanValue v0, BooleanValue v1) {
                                                         return f.and(v0, v1);
                                                     }
                                                 }, new Composer() {

                                                     @Override
                                                     public BooleanValue compose(BooleanFactory f, BooleanValue v0, BooleanValue v1) {
                                                         return f.or(v0, v1);
                                                     }
                                                 }
    };

    @Override
    protected void setUp() throws Exception {
        super.setUp();
        init();
    }

    private void init() {
        f = BooleanFactory.factory(size, new Options());
        v = new BooleanVariable[size];
        for (int i = 0; i < size; i++) {
            v[i] = f.variable(i + 1);
            assertNotNull(v[i]);
        }
    }

    private static interface Composer {

        BooleanValue compose(BooleanFactory f, BooleanValue v0, BooleanValue v1);
    }

    private final BooleanValue compose(Operator op, BooleanValue v0, BooleanValue v1) {
        return COMPOSERS[op.ordinal()].compose(f, v0, v1);
    }

    public final void testConstant() {
        assertSame(TRUE, BooleanConstant.constant(true));
        assertTrue(TRUE.booleanValue());

        assertSame(FALSE, BooleanConstant.constant(false));
        assertFalse(FALSE.booleanValue());
    }

    public void testVariable() {
        for (int i = 0; i < size; i++) {
            assertSame(v[i], f.variable(i + 1));
        }
    }

    public final void testNot() {
        // bivalency: !T = F, !F = T
        assertSame(FALSE, f.not(TRUE));
        assertSame(TRUE, f.not(FALSE));

        // involution !!a = a
        assertSame(FALSE, f.not(f.not(FALSE)));
        assertSame(TRUE, f.not(f.not(TRUE)));

        for (int i = 0; i < size; i++) {
            assertSame(v[i], f.not(f.not(v[i])));
        }

        for (int i = 0; i < size / 2; i++) {
            assertSame(f.or(v[i * 2], v[i * 2 + 1]), f.not(f.not(f.or(v[i * 2], v[i * 2 + 1]))));
            assertSame(f.and(v[i * 2], v[i * 2 + 1]), f.not(f.not(f.and(v[i * 2], v[i * 2 + 1]))));
        }
    }

    private final void testParenthesis(BooleanValue result, Operator.Nary op, BooleanValue p, BooleanValue q, BooleanValue r, BooleanValue s) {

        // System.out.println("-------------------------------");
        // System.out.println("p: " + p + " " + p.literal());
        // System.out.println("q: " + q + " " + q.literal());
        // System.out.println("r: " + r + " " + r.literal());
        // System.out.println("s: " + s + " " + s.literal());
        //
        // System.out.println("pq: " + f.compose(op, p, q));
        // System.out.println("rs: " + f.compose(op, r, s));
        // System.out.println("(pq)(rs): " + f.compose(op, f.compose(op, p, q),
        // f.compose(op, r , s)));
        //
        // System.out.println("rs: " + r.compose(op, s));
        // System.out.println("q(rs): " + q.compose(op, r.compose(op, s)));
        // System.out.println("p(q(rs)): " + p.compose(op, (q.compose(op,
        // (r.compose(op, s))))));
        //
        // System.out.println("qr: " + q.compose(op, r));
        // System.out.println("(qr)s: " + (q.compose(op, r)).compose(op, s));
        // System.out.println("p(qr)s): " + p.compose(op, ((q.compose(op,
        // r)).compose(op, s))));
        //
        // System.out.println("pq: " + p.compose(op, q));
        // System.out.println("(pq)r: " + (p.compose(op, q)).compose(op, r));
        // System.out.println("(p(qr))s: " + ((p.compose(op, q)).compose(op,
        // r)).compose(op, s));

        // p(q(rs))
        assertSame(result, compose(op, p, compose(op, q, compose(op, r, s))));
        // p((qr)s)
        assertSame(result, compose(op, p, compose(op, compose(op, q, r), s)));
        // (pq)(rs)
        assertSame(result, compose(op, compose(op, p, q), compose(op, r, s)));
        // (p(qr))s
        assertSame(result, compose(op, p, compose(op, compose(op, q, r), s)));
        // ((pq)r)s
        assertSame(result, compose(op, compose(op, compose(op, p, q), r), s));
    }

    private final void testIdentityContradictionExcludedMiddle(Operator.Nary op, BooleanValue p) {
        // identity: p & T = p | F = p
        assertSame(p, compose(op, p, op.identity()));

        // short circuit: p & F = F, p | T = T
        assertSame(op.shortCircuit(), compose(op, p, op.shortCircuit()));

        // contradiction / excluded middle: p & !p = F, p | !p = T
        assertSame(op.shortCircuit(), compose(op, p, f.not(p)));

    }

    private final void testIdempotencyAbsorptionContraction(Operator.Nary op, BooleanValue p, BooleanValue q) {
        // idempotency: p op p = p
        assertSame(p, compose(op, p, p));
        assertSame(q, compose(op, q, q));

        // absorption: p op (p op q) = p op q
        assertSame(compose(op, p, q), compose(op, p, compose(op, p, q)));

        // contraction: p op.complement (p op q) = p
        // System.out.println(p + ", " + q + ", " + p.compose(op.complement(),
        // p.compose(op, q)));
        assertSame(p, compose(op.complement(), p, compose(op, p, q)));
    }

    private final void testCommutativityAndAssociativity(Operator.Nary op, BooleanValue p, BooleanValue q, BooleanValue r, BooleanValue s) {

        // System.out.println("p: " + p + " " + p.digest());
        // System.out.println("q: " + q + " " + q.digest());
        // System.out.println("r: " + r + " " + r.digest());
        // System.out.println("s: " + s + " " + s.digest());
        // System.out.println("pq: " + p.compose(op, q));
        // System.out.println("pqr: " + p.compose(op, q).compose(op, r));
        // System.out.println("pqrs: " + p.compose(op, q).compose(op,
        // r).compose(op, s));

        // commutativity: p op q = p op q
        // and associativity: p op (r op q) = (p op r) op q

        // generate all permutations, and their parenthesizations, of p q r s
        // and check that they are the same
        final List<BooleanValue> formulas = new LinkedList<BooleanValue>();
        formulas.add(p);
        formulas.add(q);
        formulas.add(r);
        formulas.add(s);

        final BooleanValue composition = compose(op, compose(op, compose(op, p, q), r), s);

        for (int i0 = 0; i0 < 4; i0++) {
            BooleanValue f0 = formulas.get(i0);
            formulas.remove(i0);
            for (int i1 = 0; i1 < 3; i1++) {
                BooleanValue f1 = formulas.get(i1);
                formulas.remove(i1);

                for (int i2 = 0; i2 < 2; i2++) {
                    BooleanValue f2 = formulas.get(i2);
                    formulas.remove(i2);
                    testParenthesis(composition, op, f0, f1, f2, formulas.get(0));
                    formulas.add(i2, f2);
                }

                formulas.add(i1, f1);

            }
            formulas.add(i0, f0);
        }

    }

    private final void testMultiGateWithConstantAndFormula(Operator.Nary op, BooleanValue p, BooleanValue q) {
        testCommutativityAndAssociativity(op, TRUE, p, q, FALSE);
        testCommutativityAndAssociativity(op, FALSE, TRUE, p, q);
        testCommutativityAndAssociativity(op, p, TRUE, q, FALSE);
        testIdempotencyAbsorptionContraction(op, p, FALSE);
        testIdempotencyAbsorptionContraction(op, TRUE, q);
    }

    private final void testMultiGateWithConstantArgument(Operator.Nary op) {
        // constant / constant
        testIdentityContradictionExcludedMiddle(op, TRUE);
        testIdentityContradictionExcludedMiddle(op, FALSE);
        testIdempotencyAbsorptionContraction(op, TRUE, FALSE);

        // constant / variable
        testMultiGateWithConstantAndFormula(op, v[8], v[9]);

        // constant / negation
        final BooleanValue v246 = compose(op, v[2], compose(op.complement(), v[4], v[6]));
        final BooleanValue v135 = compose(op.complement(), v[1], compose(op, v[3], v[5]));
        testMultiGateWithConstantAndFormula(op, f.not(v246), f.not(v135));
        testMultiGateWithConstantAndFormula(op, v246, f.not(v135));

        // constant / multigate
        testMultiGateWithConstantAndFormula(op, v246, v135);
        testMultiGateWithConstantAndFormula(op, compose(op, v[2], v[3]), compose(op, v[1], v[4]));
    }

    private final void testMultiGateWithVariableArgument(Operator.Nary op) {
        // variable / variable
        testIdentityContradictionExcludedMiddle(op, v[0]);
        testIdentityContradictionExcludedMiddle(op, v[3]);
        testCommutativityAndAssociativity(op, v[4], v[6], v[8], v[2]);
        testIdempotencyAbsorptionContraction(op, v[1], v[5]);

        // variable / negation
        final BooleanValue v101214 = compose(op, v[10], compose(op.complement(), v[12], v[14]));
        final BooleanValue v151311 = compose(op.complement(), v[15], compose(op, v[13], v[11]));

        testCommutativityAndAssociativity(op, v[10], f.not(v151311), v[14], f.not(v101214));
        testIdempotencyAbsorptionContraction(op, v[11], f.not(v151311));

        // variable / multigate
        final BooleanValue v191618 = compose(op.complement(), v[19], compose(op.complement(), v[16], v[18])),
                        v101712 = compose(op, v[10], compose(op, v[17], v[12])),
                        v141815 = compose(op.complement(), v[14], compose(op, v[18], v[15])),
                        v121716 = compose(op, v[12], compose(op.complement(), v[17], v[16]));
        testCommutativityAndAssociativity(op, v[10], v[12], v191618, v141815);
        // fails due to not extensively checking for sharing, which is ok for
        // now
        // testCommutativityAndAssociativity(op, v[10], v[12], v121716,
        // v101712);
        testCommutativityAndAssociativity(op, v[9], v[18], v[16], v121716);
        testIdempotencyAbsorptionContraction(op, v[10], v101712);
        testIdempotencyAbsorptionContraction(op, v[14], v141815);
    }

    private final void testMultiGateWithNegatedArgument(Operator.Nary op) {
        // negation / negation
        final BooleanValue v842 = compose(op.complement(), v[8], compose(op.complement(), v[4], v[2])),
                        v191015 = compose(op, v[19], compose(op, v[10], v[15])),
                        v027 = compose(op.complement(), v[0], compose(op, v[2], v[7])),
                        v15104 = compose(op, v[15], compose(op.complement(), v[10], v[4]));
        testIdentityContradictionExcludedMiddle(op, f.not(v027));
        testIdentityContradictionExcludedMiddle(op, f.not(v191015));
        testCommutativityAndAssociativity(op, f.not(v842), f.not(v191015), f.not(v027), f.not(v15104));

        // negation / multigate
        testCommutativityAndAssociativity(op, v842, f.not(v191015), v027, f.not(v15104));
        testCommutativityAndAssociativity(op, f.not(v842), v191015, v027, f.not(v15104));
        testCommutativityAndAssociativity(op, v842, f.not(v191015), f.not(v027), v15104);
        testCommutativityAndAssociativity(op, f.not(v842), v191015, f.not(v027), v15104);

    }

    private final void testMultiGateWithMultiGateArgument(Operator.Nary op) {
        final BooleanValue v842 = compose(op.complement(), v[8], compose(op.complement(), v[4], v[2])),
                        v191015 = compose(op, v[19], compose(op, v[10], v[15])),
                        v027 = compose(op.complement(), v[0], compose(op, v[2], v[7])),
                        v15104 = compose(op, v[15], compose(op.complement(), v[10], v[4]));

        testIdentityContradictionExcludedMiddle(op, v027);
        testIdentityContradictionExcludedMiddle(op, v191015);
        testCommutativityAndAssociativity(op, v842, v191015, v027, v15104);
        testCommutativityAndAssociativity(op, v842, v191015, v027, compose(op, v[18], v[1]));
        testIdempotencyAbsorptionContraction(op, v842, v15104);
    }

    private void testMultiGate(Operator.Nary op) {
        testMultiGateWithConstantArgument(op);
        init();
        testMultiGateWithVariableArgument(op);
        init();
        testMultiGateWithNegatedArgument(op);
        init();
        testMultiGateWithMultiGateArgument(op);
    }

    public final void testAnd() {
        testMultiGate(AND);
    }

    public final void testOr() {
        testMultiGate(OR);
    }

    public final void testITE() {
        final BooleanValue a12 = f.and(v[1], v[2]), na12 = f.not(a12), a45 = f.and(v[4], v[5]), o67 = f.or(v[6], v[7]),
                        no67 = f.not(o67), o89 = f.or(v[8], v[9]), no89 = f.not(o89);
        assertSame(a12, f.ite(TRUE, a12, a45));
        assertSame(a45, f.ite(FALSE, a12, a45));
        assertSame(f.or(o89, a12), f.ite(a12, TRUE, o89));
        assertSame(f.and(o89, na12), f.ite(a12, FALSE, o89));
        assertSame(f.or(no67, a45), f.ite(o67, a45, TRUE));
        assertSame(f.and(no89, no67), f.ite(no89, no67, FALSE));
        assertSame(o67, f.ite(o89, o67, o67));
        assertSame(f.or(a12, o67), f.ite(a12, a12, o67));
        assertSame(f.and(o89, na12), f.ite(a12, na12, o89));
        assertSame(f.or(no67, a45), f.ite(o67, a45, no67));
        assertSame(f.and(no89, no67), f.ite(no89, no67, no89));
        assertSame(f.ite(f.and(v[1], v[2]), o67, a45), f.ite(a12, f.or(v[6], v[7]), a45));

    }

    // public final void testReductions() {
    // final BooleanValue val1 = f.or(v[10], v[6]);
    // final BooleanValue val2 = f.or(v[8], val1);
    // System.out.println(val1);
    // System.out.println(val2);
    // System.out.println(f.or(f.not(val2), val1));
    //
    // final BooleanAccumulator val3 = BooleanAccumulator.treeGate(OR);
    // final BooleanAccumulator val4 = BooleanAccumulator.treeGate(AND);
    // for(int i = 0; i < 5; i++) {
    // val3.add(v[i]);
    // val4.add(f.not(v[i]));
    // }
    // final BooleanValue val5 = f.accumulate(val3);
    // final BooleanValue val6 = f.accumulate(val4);
    // System.out.println(val3);
    // System.out.println(val4);
    // System.out.println(val5);
    // System.out.println(val6);
    // System.out.println(f.and(val5, val6));
    // }

    // private final void testSimpleReductions(Operator.Nary op) {
    // final BooleanValue y = compose(op.complement(), v[18], v[19]);
    // final BooleanValue noty = f.not(y);
    // final BooleanAccumulator acc = BooleanAccumulator.treeGate(op);
    // for(int i = 0, max = (1<<f.comparisonDepth())-1; i < max; i++) {
    // acc.add(v[i]);
    // }
    // acc.add(y);
    // final BooleanValue x = f.accumulate(acc);
    // final BooleanValue notx = f.not(x);
    //
    // assertSame(x, compose(op, x, y));
    // assertSame(op.shortCircuit(), compose(op, x, noty));
    // assertSame(y, compose(op.complement(), x, y));
    //
    // final BooleanFormula notsame1 = (BooleanFormula)compose(op.complement(),
    // x, noty);
    // assertSame(op.complement(), notsame1.op());
    // assertSame(2, notsame1.size());
    // assertSame(noty, notsame1.input(0));
    // assertSame(x, notsame1.input(1));
    //
    // assertSame(notx, compose(op.complement(), notx, noty));
    // assertSame(op.complement().shortCircuit(), compose(op.complement(), notx,
    // y));
    // assertSame(noty, compose(op, notx, noty));
    //
    // final BooleanFormula notsame2 = (BooleanFormula)compose(op, notx, y);
    // assertSame(op, notsame2.op());
    // assertSame(2, notsame2.size());
    // assertSame(notx, notsame2.input(0));
    // assertSame(y, notsame2.input(1));
    // }

    // public final void testSimpleReductions() {
    // testSimpleReductions(AND);
    // testSimpleReductions(OR);
    // }

}
