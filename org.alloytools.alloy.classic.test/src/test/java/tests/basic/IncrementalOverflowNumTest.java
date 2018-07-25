package tests.basic;

import static tests.basic.OverflowTestUtils.assertNoInstance;

import org.junit.Test;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.IntConstant;
import kodkod.ast.Variable;
import kodkod.engine.IncrementalSolver;
import kodkod.engine.Solution;
import kodkod.engine.config.Options;
import kodkod.instance.Bounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.Universe;

public class IncrementalOverflowNumTest extends OverflowNumTest {

    @Override
    protected Solution solve(Formula formula) {
        return IncrementalSolver.solver(options).solve(formula, bounds);
    }

    @Test
    public void testBasic() {
        Options opt = new Options();
        opt.setNoOverflow(true);
        opt.setBitwidth(2);
        IncrementalSolver solver = IncrementalSolver.solver(opt);
        Universe univ = new Universe("-2", "-1", "0", "1");
        Bounds b = new Bounds(univ);
        TupleFactory factory = univ.factory();
        b.boundExactly(-2, factory.range(factory.tuple("-2"), factory.tuple("-2")));
        b.boundExactly(-1, factory.range(factory.tuple("-1"), factory.tuple("-1")));
        b.boundExactly(0, factory.range(factory.tuple("0"), factory.tuple("0")));
        b.boundExactly(1, factory.range(factory.tuple("1"), factory.tuple("1")));
        Variable n = Variable.unary("n");
        Formula f = n.sum().plus(IntConstant.constant(1)).lte(n.sum()).forSome(n.oneOf(Expression.INTS));
        Solution sol = solver.solve(f, b);
        assertNoInstance(sol);
    }
}
