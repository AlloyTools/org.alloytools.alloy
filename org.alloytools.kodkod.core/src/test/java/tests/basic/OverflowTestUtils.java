package tests.basic;

import kodkod.ast.BinaryIntExpression;
import kodkod.ast.IntExpression;
import kodkod.ast.operator.IntOperator;
import kodkod.engine.Solution;

import static junit.framework.TestCase.assertNotNull;
import static junit.framework.TestCase.assertNull;

public class OverflowTestUtils {

    static IntExpression applyIntOp(IntOperator intOp, IntExpression lhs, IntExpression rhs) {
        return new BinaryIntExpression(lhs, intOp, rhs);
    }

    static void assertInstance(Solution[] sols) {
        for (Solution sol : sols)
            assertInstance(sol);
    }

    static void assertInstance(Solution sol) {
        assertNotNull("expected sat, actual " + sol.outcome(), sol.instance());
    }

    static void assertNoInstance(Solution[] sols) {
        for (Solution sol : sols)
            assertNoInstance(sol);
    }

    static void assertNoInstance(Solution sol) {
        assertNull("expected unsat, actual " + sol.outcome(), sol.instance());
    }

    public static int min(int bw) {
        return -(1 << (bw - 1));
    }

    public static int max(int bw) {
        return (1 << (bw - 1)) - 1;
    }
}
