package tests.basic;

import kodkod.ast.Formula;
import kodkod.engine.IncrementalSolver;
import kodkod.engine.Solution;

public class IncrementalOverflowSigTest extends OverflowSigTest {

    @Override
    protected Solution solve(Formula formula) {
        return IncrementalSolver.solver(options).solve(formula, bounds);
    }

}
