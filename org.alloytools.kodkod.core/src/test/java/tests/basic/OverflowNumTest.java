package tests.basic;

import static kodkod.ast.IntExpression.compose;
import static kodkod.ast.operator.IntOperator.DIVIDE;
import static kodkod.ast.operator.IntOperator.MINUS;
import static kodkod.ast.operator.IntOperator.MODULO;
import static kodkod.ast.operator.IntOperator.MULTIPLY;
import static kodkod.ast.operator.IntOperator.PLUS;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.junit.Test;

import junit.framework.TestCase;
import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.IntConstant;
import kodkod.ast.IntExpression;
import kodkod.ast.Relation;
import kodkod.ast.operator.IntOperator;
import kodkod.engine.Evaluator;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.config.Options;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;
import kodkod.instance.TupleFactory;
import kodkod.instance.Universe;

public class OverflowNumTest extends TestCase {

    protected final TupleFactory factory;
    protected final Relation     ret;
    protected Bounds             bounds;
    protected Options            options;

    private static final int     DEF_VAL = -1;

    @SuppressWarnings("serial" )
    public class NoSol extends RuntimeException {}

    public abstract class Tester {

        public abstract void doTest(int i, int j);
    }

    public abstract class GenericTester extends Tester {

        public void doTmpTest() {
            int bw = 5, l = -(1 << (bw - 1)), h = (1 << (bw - 1));
            IntOperator[] ops = new IntOperator[] {
                                                   PLUS, MINUS, MULTIPLY, DIVIDE, MODULO
            };
            for (IntOperator op : ops)
                for (int i = l; i < h; i++)
                    for (int j = l; j < h; j++) {
                        Formula f = ret.eq(compose(op, IntConstant.constant(i), IntConstant.constant(j)).toExpression());
                        int javaResult = -1;
                        try {
                            javaResult = exeJava(op, i, j);
                        } catch (ArithmeticException e) {
                            continue;
                        }
                        if (javaResult >= h || javaResult < l) {
                            try {
                                int kkResult = exeKodkod(f);
                                fail(String.format("Overflow not detected: (%s) %s (%s) != %s", i, op, j, kkResult));
                            } catch (NoSol e) {}
                        } else {
                            try {
                                int kkResult = exeKodkod(f);
                                assertEquals(String.format("Wrong result: (%s) %s (%s) != %s", i, op, j, kkResult), javaResult, kkResult);
                            } catch (NoSol e) {
                                fail(String.format("No solution for (%s) %s (%s); expected: %s", i, op, j, javaResult));
                            }
                        }
                    }
        }

        private int exeKodkod(Formula f) {
            Solution sol = solve(f);
            return eval(sol.instance());
        }

        private int exeJava(IntOperator op, int i, int j) {
            switch (op) {
                case PLUS :
                    return i + j;
                case MINUS :
                    return i - j;
                case MULTIPLY :
                    return i * j;
                case DIVIDE :
                    return i / j;
                case MODULO :
                    return i % j;
                default :
                    throw new RuntimeException("unknown op: " + op);
            }
        }

        // ===================================

        @Override
        public void doTest(int i, int j) {
            doTestNoDef(i, j);
            doTestDef(i, j);
        }

        protected void doTestDef(int i, int j) {
            int min = min();
            int max = max();
            String op = getOp();
            int res;
            boolean of = false;
            try {
                res = exeJava(i, j);
                if (res > max || res < min) {
                    of = true;
                    res = DEF_VAL;
                }
            } catch (Exception e) {
                of = true;
                res = DEF_VAL;
            }
            try {
                int x = exeKodkodDef(i, j);
                String msg = of ? String.format("Expected the default value (%d) due to overflow ((%d) %s (%d)) but got %d", DEF_VAL, i, op, j, x) : String.format("Wrong result: %s %s %s != %s", i, op, j, x);
                assertEquals(msg, res, x);
            } catch (NoSol e) {
                String msg = String.format("Expected the default value (%d) due to overflow (%d %s %d) but got exception: %s", DEF_VAL, i, op, j, e.getClass().getSimpleName() + ": " + e.getMessage());
                fail(msg);
            }
        }

        protected void doTestNoDef(int i, int j) {
            if (skip(i, j))
                return;
            int min = min();
            int max = max();
            String op = getOp();
            int res = exeJava(i, j);
            if (res > max || res < min) {
                try {
                    int x = exeKodkod(i, j);
                    fail(String.format("Overflow not detected: (%s) %s (%s) != %s", i, op, j, x));
                } catch (NoSol e) {}
            } else {
                try {
                    int x = exeKodkod(i, j);
                    assertEquals(String.format("Wrong result: (%s) %s (%s) != %s", i, op, j, x), res, x);
                } catch (NoSol e) {
                    fail(String.format("No solution for (%s) %s (%s); expected: %s", i, op, j, res));
                }
            }
        }

        protected int eval(Instance instance) {
            if (instance == null)
                throw new NoSol();
            Evaluator ev = new Evaluator(instance);
            return Integer.parseInt(ev.evaluate(ret).iterator().next().atom(0).toString());
        }

        protected int exeKodkod(int i, int j) {
            Formula f = ret.eq(kodkodOpExpr(IntConstant.constant(i), IntConstant.constant(j)).toExpression());
            Solution sol = solve(f);
            return eval(sol.instance());
        }

        protected int exeKodkodDef(int i, int j) {
            IntExpression kkIntExpr = kodkodOpExpr(IntConstant.constant(i), IntConstant.constant(j));
            Expression kkExpr = kkIntExpr.toExpression();
            Formula f = ret.eq(kkExpr.some().thenElse(kkIntExpr.toExpression(), IntConstant.constant(DEF_VAL).toExpression()));
            Solution sol = solve(f);
            return eval(sol.instance());
        }

        protected abstract int exeJava(int i, int j);

        protected abstract IntExpression kodkodOpExpr(IntExpression i, IntExpression j);

        protected abstract String getOp();

        protected boolean skip(int i, int j) {
            return false;
        }
    }

    public OverflowNumTest() {
        this.ret = Relation.unary("ret");
        int min = min();
        int max = max();
        List<String> atoms = new ArrayList<String>(max - min + 1);
        for (int i = min; i <= max; i++) {
            atoms.add(String.valueOf(i));
        }
        final Universe universe = new Universe(atoms);
        this.factory = universe.factory();
        this.bounds = new Bounds(factory.universe());
        for (int i = min; i <= max; i++) {
            bounds.boundExactly(i, factory.setOf(String.valueOf(i)));
        }
        bounds.bound(ret, factory.noneOf(1), factory.allOf(1));
    }

    protected int bw() {
        return 5;
    }

    @Override
    protected void setUp() throws Exception {
        super.setUp();
        setupOptions();
    }

    protected void setupOptions() {
        options = new Options();
        options.setNoOverflow(true);
        options.setBitwidth(bw());
        options.setSolver(SATFactory.MiniSat);
    }

    @Override
    protected void tearDown() throws Exception {
        super.tearDown();
    }

    protected Solution solve(Formula formula) {
        return new Solver(options).solve(formula, bounds);
    }

    protected Iterator<Solution> solveAll(Formula formula) {
        return new Solver(options).solveAll(formula, bounds);
    }

    @Test
    public void testPlus() {
        runTestForAll(new GenericTester() {

            @Override
            protected int exeJava(int i, int j) {
                return i + j;
            }

            @Override
            protected IntExpression kodkodOpExpr(IntExpression i, IntExpression j) {
                return i.plus(j);
            }

            @Override
            protected String getOp() {
                return "+";
            }
        });
    }

    @Test
    public void testMinus() {
        runTestForAll(new GenericTester() {

            @Override
            protected int exeJava(int i, int j) {
                return i - j;
            }

            @Override
            protected IntExpression kodkodOpExpr(IntExpression i, IntExpression j) {
                return i.minus(j);
            }

            @Override
            protected String getOp() {
                return "-";
            }
        });
    }

    @Test
    public void testTimes() {
        runTestForAll(new GenericTester() {

            @Override
            protected int exeJava(int i, int j) {
                return i * j;
            }

            @Override
            protected IntExpression kodkodOpExpr(IntExpression i, IntExpression j) {
                return i.multiply(j);
            }

            @Override
            protected String getOp() {
                return "*";
            }
        });
    }

    @Test
    public void testDiv() {
        runTestForAll(new GenericTester() {

            @Override
            protected int exeJava(int i, int j) {
                return i / j;
            }

            @Override
            protected IntExpression kodkodOpExpr(IntExpression i, IntExpression j) {
                return i.divide(j);
            }

            @Override
            protected String getOp() {
                return "/";
            }

            @Override
            protected boolean skip(int i, int j) {
                return j == 0;
            }
        });
    }

    @Test
    public void testMod() {
        runTestForAll(new GenericTester() {

            @Override
            protected int exeJava(int i, int j) {
                return i % j;
            }

            @Override
            protected IntExpression kodkodOpExpr(IntExpression i, IntExpression j) {
                return i.modulo(j);
            }

            @Override
            protected String getOp() {
                return "%";
            }

            @Override
            protected boolean skip(int i, int j) {
                return j == 0;
            }
        });
    }

    @Test
    public void testTmp() {
        new GenericTester() {

            @Override
            protected IntExpression kodkodOpExpr(IntExpression i, IntExpression j) {
                return null;
            }

            @Override
            protected String getOp() {
                return null;
            }

            @Override
            protected int exeJava(int i, int j) {
                return 0;
            }
        }.doTmpTest();
    }

    protected void runTestForAll(Tester t) {
        int min = min();
        int max = max();
        for (int i = min; i <= max; i++) {
            for (int j = min; j <= max; j++) {
                t.doTest(i, j);
            }
        }
    }

    protected int min() {
        return -(1 << (bw() - 1));
    }

    protected int max() {
        return (1 << (bw() - 1)) - 1;
    }

}
