package tests.basic;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import org.junit.Test;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.Evaluator;
import kodkod.engine.Solution;
import kodkod.instance.Bounds;

public class OverflowEnumTest extends OverflowNumTest {

    private Bounds     superBounds;

    protected Relation op1;
    protected Relation op2;

    public OverflowEnumTest() {
        super();
        this.superBounds = bounds;
    }

    @Override
    protected int bw() {
        return 4;
    }

    class Res {

        public final int op1, op2, res;

        public Res(int op1, int op2, int res) {
            this.op1 = op1;
            this.op2 = op2;
            this.res = res;
        }

        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result + getOuterType().hashCode();
            result = prime * result + op1;
            result = prime * result + op2;
            result = prime * result + res;
            return result;
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj)
                return true;
            if (obj == null)
                return false;
            if (getClass() != obj.getClass())
                return false;
            Res other = (Res) obj;
            if (!getOuterType().equals(other.getOuterType()))
                return false;
            if (op1 != other.op1)
                return false;
            if (op2 != other.op2)
                return false;
            if (res != other.res)
                return false;
            return true;
        }

        private OverflowEnumTest getOuterType() {
            return OverflowEnumTest.this;
        }
    }

    @Test
    @Override
    public void testTmp() {}

    @Override
    protected void runTestForAll(Tester t) {
        GenericTester gt = (GenericTester) t;
        this.op1 = Relation.unary("a");
        this.op2 = Relation.unary("b");
        bounds = superBounds.clone();
        bounds.bound(op1, factory.noneOf(1), factory.allOf(1));
        bounds.bound(op2, factory.noneOf(1), factory.allOf(1));

        Formula goal = op1.one().and(op2.one()).and(ret.one());
        // goal = goal.and(ret.sum().eq(gt.kodkodOpExpr(op1.sum(), op2.sum())));
        goal = goal.and(ret.eq(gt.kodkodOpExpr(op1.sum(), op2.sum()).toExpression()));
        Set<Res> kkRes = new HashSet<Res>();
        Iterator<Solution> sols = solveAll(goal);
        while (sols.hasNext()) {
            Solution sol = sols.next();
            if (sol.unsat())
                break;
            Evaluator evaluator = new Evaluator(sol.instance());
            int ia = evalInt(evaluator, op1);
            int ib = evalInt(evaluator, op2);
            int ir = evalInt(evaluator, ret);
            kkRes.add(new Res(ia, ib, ir));
        }

        Set<Res> jRes = new HashSet<Res>();
        int min = min();
        int max = max();
        for (int i = min; i <= max; i++) {
            for (int j = min; j <= max; j++) {
                if (gt.skip(i, j))
                    continue;
                int res = gt.exeJava(i, j);
                if (res < min || res > max)
                    continue;
                jRes.add(new Res(i, j, res));
            }
        }

        assertEquals(kkRes, jRes);
    }

    protected int evalInt(Evaluator ev, Expression a) {
        return Integer.parseInt(ev.evaluate(a).iterator().next().atom(0).toString());
    }

}
