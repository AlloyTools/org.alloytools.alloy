package tests.basic;

import static tests.basic.OverflowTestUtils.assertInstance;
import static tests.basic.OverflowTestUtils.assertNoInstance;
import static tests.basic.OverflowTestUtils.max;
import static tests.basic.OverflowTestUtils.min;

import java.util.ArrayList;
import java.util.List;

import org.junit.Test;

import junit.framework.TestCase;
import kodkod.ast.Decls;
import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.IntConstant;
import kodkod.ast.IntExpression;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.config.Options;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.Universe;

public class OverflowTheoremTest extends TestCase {

    private final int     bw = 5;

    private Options       options;

    protected IntConstant ZERO;
    protected IntConstant MININT, MAXINT;
    private Variable      a;
    private Variable      b;
    private IntExpression as;
    private IntExpression bs;
    private Decls         decls;

    private Bounds        bounds;

    @Override
    protected void setUp() throws Exception {
        super.setUp();
        setupOptions();
        setupBounds();

        ZERO = IntConstant.constant(0);
        MININT = IntConstant.constant(min(bw));
        MAXINT = IntConstant.constant(max(bw));
        a = Variable.unary("a");
        b = Variable.unary("b");
        as = a.sum();
        bs = b.sum();
        decls = a.oneOf(Expression.INTS).and(b.oneOf(Expression.INTS));
    }

    protected void setupBounds() {
        Relation ret = Relation.unary("ret");
        int min = min(bw);
        int max = max(bw);
        List<String> atoms = new ArrayList<String>(max - min + 1);
        for (int i = min; i <= max; i++) {
            atoms.add(String.valueOf(i));
        }
        final Universe universe = new Universe(atoms);
        TupleFactory factory = universe.factory();
        this.bounds = new Bounds(factory.universe());
        for (int i = min; i <= max; i++) {
            bounds.boundExactly(i, factory.setOf(String.valueOf(i)));
        }
        bounds.bound(ret, factory.noneOf(1), factory.allOf(1));
    }

    protected void setupOptions() {
        options = new Options();
        options.setNoOverflow(true);
        options.setBitwidth(bw);
        options.setSolver(SATFactory.MiniSat);
        options.setSkolemDepth(0);
    }

    @Override
    protected void tearDown() throws Exception {
        super.tearDown();
    }

    protected Solution[] solve(Formula formula) {
        Solution s1 = new Solver(options).solve(formula, bounds);
        Options opt2 = options.clone();
        opt2.setSkolemDepth(2);
        // Solution s2 = new Solver(opt2).solve(formula, bounds);
        return new Solution[] {
                               s1
        };
    }

    protected void checkTrue(Formula f) {
        assertNoInstance(solve(f.not()));
    }

    protected void checkFalse(Formula f) {
        assertInstance(solve(f.not()));
    }

    protected void checkSat(Formula f) {
        assertInstance(solve(f));
    }

    protected void checkUnsat(Formula f) {
        assertNoInstance(solve(f));
    }

    /**
     * all decl | pre => post !!(all decl | pre => post) all decl | !!(pre => post)
     * all decl | !(pre && !post) all decl | !pre || post !(some decl | !(pre =>
     * post)) !!!(some decl | !(pre => post)) !(some decl | pre && !post) !(some
     * decl | !!(pre && !post)) !(some decl | !(!pre || post))
     */
    protected void checkTrue(Formula pre, Formula post, Decls forAllDecls) {
        Formula f = pre.implies(post).forAll(forAllDecls);
        checkTrue(f);

        f = pre.implies(post).forAll(forAllDecls).not().not();
        checkTrue(f);

        f = pre.implies(post).not().not().forAll(forAllDecls);
        checkTrue(f);

        f = pre.and(post.not()).not().forAll(forAllDecls);
        checkTrue(f);

        f = pre.not().or(post).forAll(forAllDecls);
        checkTrue(f);

        f = pre.implies(post).not().forSome(forAllDecls).not().not().not();
        checkTrue(f);

        f = pre.implies(post).not().forSome(forAllDecls).not();
        checkTrue(f);

        f = pre.and(post.not()).forSome(forAllDecls).not();
        checkTrue(f);

        f = pre.and(post.not()).not().not().forSome(forAllDecls).not();
        checkTrue(f);

        f = pre.not().or(post).not().forSome(forAllDecls).not();
        checkTrue(f);
    }

    /**
     * all s : set univ | #s >= 0 !some(s : set univ | #s < 0)
     */
    @Test
    public void testCardinality0() {
        Variable s = Variable.unary("s");
        Formula f = (s.count().gte(IntConstant.constant(0))).forAll(s.setOf(Expression.UNIV));
        checkTrue(f);

        f = (s.count().lt(IntConstant.constant(0))).forSome(s.setOf(Expression.UNIV)).not();
        checkTrue(f);
    }

    /**
     * all s : set univ | (some s) iff #s > 0
     */
    @Test
    public void testCardinality1() {
        Variable s = Variable.unary("s");
        Formula f = s.some().iff(s.count().gt(IntConstant.constant(0))).forAll(s.setOf(Expression.UNIV));
        checkTrue(f);
    }

    /**
     * all s, t : set univ | #(s + t) >= #s && #(s + t) >= #t
     */
    @Test
    public void testCardinality2() {
        Variable s = Variable.unary("s");
        Variable t = Variable.unary("t");
        IntExpression sutCnt = s.union(t).count();
        Decls dcls = s.setOf(Expression.UNIV).and(t.setOf(Expression.UNIV));
        Formula f = sutCnt.gte(s.count()).and(sutCnt.gte(t.count())).forAll(dcls);
        checkTrue(f);
    }

    /**
     * all a, b: set univ | a in b => #a <= #b
     */
    @Test
    public void testCardinality3() {
        Variable a = Variable.unary("a");
        Variable b = Variable.unary("b");
        Decls dcls = a.setOf(Expression.UNIV).and(b.setOf(Expression.UNIV));
        Formula pre = a.in(b);
        Formula post = a.count().lte(b.count());
        checkTrue(pre, post, dcls);
    }

    /**
     * all a, b: set univ | no a & b && some a => #(a + b) > #b
     */
    @Test
    public void testCardinality4() {
        Variable a = Variable.unary("a");
        Variable b = Variable.unary("b");
        Decls dcls = a.setOf(Expression.UNIV).and(b.setOf(Expression.UNIV));
        Formula pre = a.some().and(a.intersection(b).no());
        Formula post = a.union(b).count().gt(b.count());
        checkTrue(pre, post, dcls);
    }

    /**
     * all a, b: Int | a > 0 && b > 0 => a + b > 0 && a + b > a && a + b > b all a,
     * b: Int | a < 0 && b < 0 => a + b < 0 && a + b < a && a + b < b
     */
    @Test
    public void testTh1() {
        {
            Formula pre = as.gt(ZERO).and(bs.gt(ZERO));
            IntExpression apb = as.plus(bs);
            Formula post = apb.gt(ZERO).and(apb.gt(as)).and(apb.gt(bs));
            checkTrue(pre, post, decls);
        }
        {
            Formula pre = as.lt(ZERO).and(bs.lt(ZERO));
            IntExpression apb = as.plus(bs);
            Formula post = apb.lt(ZERO).and(apb.lt(as)).and(apb.lt(bs));
            checkTrue(pre, post, decls);
        }
    }

    /**
     * all a, b: Int | a > 0 && b < 0 => a - b > 0 && a - b > a && a - b > b all a,
     * b: Int | a < 0 && b > 0 => a - b < 0 && a - b < a && a - b < b
     */
    @Test
    public void testTh2() {
        {
            Formula pre = as.gt(ZERO).and(bs.lt(ZERO));
            IntExpression amb = as.minus(bs);
            Formula post = amb.gt(ZERO).and(amb.gt(as)).and(amb.gt(bs.negate()));
            checkTrue(pre, post, decls);
        }
        {
            Formula pre = as.lt(ZERO).and(bs.gt(ZERO));
            IntExpression amb = as.minus(bs);
            Formula post = amb.lt(ZERO).and(amb.lt(as)).and(amb.lt(bs.negate()));
            checkTrue(pre, post, decls);
        }
    }

    /**
     * all a, b: Int | a > 0 && b > 0 => a * b > 0 && a * b >= a && a * b >= b all
     * a, b: Int | a < 0 && b < 0 => a * b > 0 && a * b >= -a && a * b >= -b
     */
    @Test
    public void testTh3() {
        {
            Formula pre = as.gt(ZERO).and(bs.gt(ZERO));
            IntExpression atb = as.multiply(bs);
            Formula post = atb.gt(ZERO).and(atb.gte(as)).and(atb.gte(bs));
            checkTrue(pre, post, decls);
        }
        {
            Formula pre = as.lt(ZERO).and(bs.lt(ZERO));
            IntExpression atb = as.multiply(bs);
            Formula post = atb.gt(ZERO).and(atb.gte(as.negate())).and(atb.gte(bs.negate()));
            checkTrue(pre, post, decls);
        }
    }

    /**
     * all a, b: Int | a > 0 && b < 0 => a * b < 0 && -(a * b) > a && -(a * b) > -b
     * all a, b: Int | a < 0 && b > 0 => a * b < 0 && -(a * b) > -a && -(a * b) > b
     */
    @Test
    public void testTh4() {
        {
            Formula pre = as.gt(ZERO).and(bs.lt(ZERO));
            IntExpression atb = as.multiply(bs);
            Formula post = atb.lt(ZERO).and(atb.negate().gte(as)).and(atb.negate().gte(bs.negate()));
            checkTrue(pre, post, decls);
        }
        {
            Formula pre = as.lt(ZERO).and(bs.gt(ZERO));
            IntExpression atb = as.multiply(bs);
            Formula post = atb.lt(ZERO).and(atb.negate().gte(as.negate())).and(atb.negate().gte(bs));
            checkTrue(pre, post, decls);
        }
    }

    /**
     * UNSAT: all a: Int | some b: Int | b = MAXINT && (a = MAXINT => a+a = b+b)
     * UNSAT !(some a: Int | all b: Int | !(b = MAXINT && (a = MAXINT => a+a =
     * b+b))) UNSAT: some b: Int | all a: Int | b = MAXINT && (a = MAXINT => a+a =
     * b+b) UNSAT: !(all b: Int | some a: Int | !(b = MAXINT && (a = MAXINT => a+a =
     * b+b))) ---- UNSAT: all x: Int | all a: Int | some b: Int | b = MAXINT && (a =
     * MAXINT => a+a = b+b) UNSAT !(some x: Int | some a: Int | all b: Int | !(b =
     * MAXINT && (a = MAXINT => a+a = b+b))) UNSAT: all x: Int | some b: Int | all
     * a: Int | b = MAXINT && (a = MAXINT => a+a = b+b) UNSAT: !(some x: Int | all
     * b: Int | some a: Int | !(b = MAXINT && (a = MAXINT => a+a = b+b)))
     */
    public void testUnsat() {
        Formula body = bs.eq(MAXINT).and(as.eq(MAXINT).implies(as.plus(as).eq(bs.plus(bs))));

        checkUnsat(body.forSome(b.oneOf(Expression.INTS)).forAll(a.oneOf(Expression.INTS)));
        checkUnsat(body.not().forAll(b.oneOf(Expression.INTS)).forSome(a.oneOf(Expression.INTS)).not());

        checkUnsat(body.forAll(a.oneOf(Expression.INTS)).forSome(b.oneOf(Expression.INTS)));
        checkUnsat(body.not().forSome(a.oneOf(Expression.INTS)).forAll(b.oneOf(Expression.INTS)).not());

        Variable x = Variable.unary("x");

        checkUnsat(body.forSome(b.oneOf(Expression.INTS)).forAll(a.oneOf(Expression.INTS)).forAll(x.oneOf(Expression.INTS)));
        checkUnsat(body.not().forAll(b.oneOf(Expression.INTS)).forSome(a.oneOf(Expression.INTS)).forSome(x.oneOf(Expression.INTS)).not());

        checkUnsat(body.forAll(a.oneOf(Expression.INTS)).forSome(b.oneOf(Expression.INTS)).forAll(x.oneOf(Expression.INTS)));
        checkUnsat(body.not().forSome(a.oneOf(Expression.INTS)).forAll(b.oneOf(Expression.INTS)).forSome(x.oneOf(Expression.INTS)).not());
    }

    /**
     * UNSAT: all a: Int | some b: Int | b = MAXINT && (a = MAXINT => (a + b = a +
     * b)) SAT: some a: Int | all b: Int | b = MAXINT && (a = MAXINT => (a + b = a +
     * b))
     */
    public void testSatUnsat() {
        Formula body = bs.eq(MAXINT).and(as.eq(MAXINT).implies(as.plus(bs).eq(as.plus(bs))));
        checkUnsat(body.forSome(b.oneOf(Expression.INTS)).forAll(a.oneOf(Expression.INTS)));
        checkSat(body.forAll(a.oneOf(Expression.INTS)).forSome(b.oneOf(Expression.INTS)));
    }

    /**
     * UNSAT: all a: Int | some b: Int | b = MAXINT && (a = MAXINT => a+a = b+b)
     * UNSAT: some a: Int | all b: Int | b = MAXINT && (a = MAXINT => a+a = b+b)
     */
    public void testUnsatUnsat() {
        Formula body = bs.eq(MAXINT).and(as.eq(MAXINT).implies(as.plus(as).eq(bs.plus(bs))));
        checkUnsat(body.forSome(b.oneOf(Expression.INTS)).forAll(a.oneOf(Expression.INTS)));
        checkUnsat(body.forAll(b.oneOf(Expression.INTS)).forSome(a.oneOf(Expression.INTS)));
    }

    /**
     * SAT: all a: Int | all b: Int | b = MAXINT => (a = MAXINT => a+a = b+b) SAT:
     * !(some a: Int | some b: Int | !(b = MAXINT => (a = MAXINT => a+a = b+b))
     */
    public void testSat() {
        Formula body = bs.eq(MAXINT).implies(as.eq(MAXINT).implies(as.plus(as).eq(bs.plus(bs))));
        checkSat(body.forAll(b.oneOf(Expression.INTS)).forAll(a.oneOf(Expression.INTS)));
        checkSat(body.not().forSome(b.oneOf(Expression.INTS)).forSome(a.oneOf(Expression.INTS)).not());
    }

    public void test2() {
        Formula body = bs.eq(MAXINT).and(as.eq(MAXINT).implies(as.plus(as).eq(bs.plus(bs))));
        Formula qf = body.forSome(b.oneOf(Expression.INTS)).forAll(a.oneOf(Expression.INTS));
        checkSat(qf.implies(ZERO.eq(ZERO)));
        checkSat(qf.implies(ZERO.neq(ZERO)));

        checkSat(qf.not().implies(ZERO.eq(ZERO)));
        checkUnsat(qf.not().implies(ZERO.neq(ZERO)));

        Formula qfnot = body.not().forAll(b.oneOf(Expression.INTS)).forSome(a.oneOf(Expression.INTS));
        checkSat(qfnot.implies(ZERO.eq(ZERO)));
        checkUnsat(qfnot.implies(ZERO.neq(ZERO)));
    }
}
