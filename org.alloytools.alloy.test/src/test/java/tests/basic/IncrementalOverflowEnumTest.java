package tests.basic;

import java.util.Iterator;

import kodkod.ast.Formula;
import kodkod.ast.IntConstant;
import kodkod.engine.Evaluator;
import kodkod.engine.IncrementalSolver;
import kodkod.engine.Solution;
import kodkod.instance.Bounds;

public class IncrementalOverflowEnumTest extends OverflowEnumTest {

    @Override
    protected Solution solve(Formula formula) {
        return IncrementalSolver.solver(options).solve(formula, bounds);
    }

    @Override
    protected Iterator<Solution> solveAll(final Formula formula) {
        final IncrementalSolver solver = IncrementalSolver.solver(options);
        return new Iterator<Solution>() {

            Solution sol;

            @Override
            public boolean hasNext() {
                return sol == null || sol.sat();
            }

            @Override
            public Solution next() {
                if (sol == null) {
                    sol = solver.solve(formula, bounds);
                } else {
                    Evaluator ev = new Evaluator(sol.instance());
                    int a = evalInt(ev, op1);
                    int b = evalInt(ev, op2);
                    int r = evalInt(ev, ret);
                    Formula f = op1.eq(IntConstant.constant(a).toExpression()).and(op2.eq(IntConstant.constant(b).toExpression())).and(ret.eq(IntConstant.constant(r).toExpression())).not();
                    sol = solver.solve(f, new Bounds(factory.universe()));
                }
                return sol;
            }

            @Override
            public void remove() {
                throw new RuntimeException("Not supported");
            }

        };
    }

}
