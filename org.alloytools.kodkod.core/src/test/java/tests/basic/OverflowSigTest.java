package tests.basic;

import static tests.basic.OverflowTestUtils.applyIntOp;
import static tests.basic.OverflowTestUtils.assertInstance;
import static tests.basic.OverflowTestUtils.assertNoInstance;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.junit.Test;

import junit.framework.TestCase;
import kodkod.ast.Formula;
import kodkod.ast.IntExpression;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.ast.operator.IntOperator;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.config.Options;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

public class OverflowSigTest extends TestCase {

    interface Func {

        IntExpression call(IntExpression lhs, IntExpression rhs);
    }

    protected Options      options;
    protected TupleFactory factory;
    protected Bounds       bounds;

    private Relation       s, x, sa, sb, sc;
    private List<String>   sAtoms, xAtoms;
    private Formula        facts;
    private Formula        check;
    private Formula        goal;
    private Solution       sol;

    @Override
    protected void setUp() throws Exception {
        super.setUp();
    }

    @Override
    protected void tearDown() throws Exception {
        super.tearDown();
    }

    protected Solution solve(Formula formula) {
        return new Solver(options).solve(formula, bounds);
    }

    protected void checkTrue(Formula f) {
        assertNoInstance(solve(f.not()));
    }

    protected void checkFalse(Formula f) {
        assertInstance(solve(f.not()));
    }

    protected void createRelations() {
        s = Relation.unary("S");
        x = Relation.unary("X");
        sa = Relation.binary("sa");
        sb = Relation.binary("sb");
        sc = Relation.binary("sc");
    }

    /**
     * sAtoms = [S0, S1, ..., S<numS-1>] xAtoms = [X0, X1, ..., S<numX-1>]
     */
    protected void createAtoms(int numS, int numX) {
        sAtoms = new ArrayList<String>(numS);
        xAtoms = new ArrayList<String>(numX);
        for (int i = 0; i < numS; i++)
            sAtoms.add(String.format("S%d", i));
        for (int i = 0; i < numX; i++)
            xAtoms.add(String.format("X%d", i));
    }

    protected void createBounds() {
        Collection<String> atoms = new ArrayList<String>(sAtoms.size() + xAtoms.size());
        atoms.addAll(sAtoms);
        atoms.addAll(xAtoms);
        final Universe universe = new Universe(atoms);
        this.factory = universe.factory();
        this.bounds = new Bounds(universe);
        TupleSet sTs = factory.setOf(sAtoms.toArray());
        TupleSet xTs = factory.setOf(xAtoms.toArray());
        bounds.bound(s, sTs);
        bounds.bound(x, xTs);
        bounds.bound(sa, sTs.product(xTs));
        bounds.bound(sb, sTs.product(xTs));
        bounds.bound(sc, sTs.product(xTs));
    }

    /**
     * all v: S | <int_op>[#s.sa, #s.sb] = #s.sc <int_op> = {plus, minus, times,
     * div, mod}
     */
    protected void createFacts(IntOperator intOp) {
        Variable vs = Variable.unary("vs");
        Formula body = applyIntOp(intOp, vs.join(sa).count(), vs.join(sb).count()).eq(vs.join(sc).count());
        this.facts = body.forAll(vs.oneOf(s));
    }

    protected void createOptions(int bw) {
        this.options = new Options();
        options.setNoOverflow(true);
        options.setBitwidth(bw);
        options.setSolver(SATFactory.MiniSat);
    }

    /**
     * some s.sa && some s.sb => some.sc
     */
    protected void createCheck() {
        Variable vs = Variable.unary("s");
        Formula body = vs.join(sa).some().and(vs.join(sb).some()).implies(vs.join(sc).some());
        this.check = body.forAll(vs.oneOf(s));
    }

    protected Solution check() {
        this.goal = facts.and(check.not());
        this.sol = solve(goal);
        return sol;
    }

    public Solution checkForBw(IntOperator intOp, int bw) {
        createRelations();
        createAtoms(1, 8);
        createBounds();
        createFacts(intOp);
        createOptions(bw);
        createCheck();
        return check();
    }

    @Test
    public void testOverBw() {
        IntOperator[] ops = new IntOperator[] {
                                               IntOperator.PLUS, IntOperator.MULTIPLY
        };
        for (IntOperator op : ops) {
            for (int i = 1; i < 6; i++) {
                Solution solution = checkForBw(op, i);
                assertNoInstance(solution);
            }
        }
    }

}
