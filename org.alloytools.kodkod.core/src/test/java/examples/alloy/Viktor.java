/**
 *
 */
package examples.alloy;

import static kodkod.ast.Expression.INTS;

import java.util.ArrayList;
import java.util.List;

import kodkod.ast.Decls;
import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.IntConstant;
import kodkod.ast.IntExpression;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.Evaluator;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.config.ConsoleReporter;
import kodkod.engine.config.Options;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

/**
 * A KK encoding of the Kuncak hypothesis for n = 3.
 *
 * @author Emina Torlak
 */
public final class Viktor {

    private final int             rows, cols;
    private final Relation[][]    a;
    private final Relation[]      x;
    private final IntExpression[] b;

    /**
     * Constructs an instance of Viktor for n = 3.
     */
    public Viktor() {
        rows = 3;
        cols = 1 << rows;
        a = new Relation[rows][cols];
        x = new Relation[cols];
        b = new IntExpression[rows];
        for (int i = 0; i < rows; i++) {
            for (int j = 0; j < cols; j++) {
                a[i][j] = Relation.unary("a" + String.valueOf(i) + String.valueOf(j));
            }
        }
        for (int j = 0; j < cols; j++) {
            x[j] = Relation.unary("x" + j);
        }
        for (int i = 0; i < rows; i++) {
            b[i] = conditionalSum(a[i], x, 0, cols - 1);
        }
    }

    /**
     * Returns the sum of the elements in x (conditional on the non-emptiness of a
     * given a[i]) located at indices [lo..hi]
     *
     * @return the sum of cardinalities of the elements in x (conditional on the
     *         non-emptiness of a given a[i]) located at indices [lo..hi]
     */
    private static IntExpression conditionalSum(Expression[] a, Expression[] x, int lo, int hi) {
        if (lo > hi)
            return IntConstant.constant(0);
        else if (lo == hi)
            return a[lo].some().thenElse(x[lo].sum(), IntConstant.constant(0));
        else {
            final int mid = (lo + hi) / 2;
            final IntExpression lsum = conditionalSum(a, x, lo, mid);
            final IntExpression hsum = conditionalSum(a, x, mid + 1, hi);
            return lsum.plus(hsum);
        }
    }

    /**
     * Returns a formula constraining all x's to be singletons.
     *
     * @return a formula constraining all x's to be singletons
     */
    public final Formula decls() {
        Formula ret = Formula.TRUE;
        for (Relation xj : x) {
            ret = ret.and(xj.one());
        }
        return ret;
    }

    /**
     * Returns the equations to be satisfied.
     *
     * @return equations to be satisfied.
     */
    public final Formula equations() {

        // each b <= cols-1
        Formula f0 = Formula.TRUE;
        final IntConstant colConst = IntConstant.constant(cols - 1);
        for (IntExpression bi : b) {
            f0 = f0.and(bi.lte(colConst));
        }

        final Variable[] y = new Variable[rows];
        for (int i = 0; i < rows; i++) {
            y[i] = Variable.unary("y" + i);
        }

        Decls decls = y[0].oneOf(INTS);
        for (int i = 1; i < rows; i++)
            decls = decls.and(y[i].oneOf(INTS));

        Formula f1 = Formula.TRUE;
        final Expression[] combo = new Expression[rows];
        for (int i = 0; i < cols; i++) {
            for (int j = i + 1; j < cols; j++) {
                for (int k = j + 1; k < cols; k++) {
                    Formula f2 = Formula.TRUE;
                    for (int m = 0; m < rows; m++) {
                        combo[0] = a[m][i];
                        combo[1] = a[m][j];
                        combo[2] = a[m][k];
                        f2 = f2.and(conditionalSum(combo, y, 0, rows - 1).eq(b[m]));
                    }
                    f1 = f1.and(f2.not().forAll(decls));
                }
            }
        }
        return f0.and(f1);
    }

    /**
     * Returns decls() && equations().
     *
     * @return decls() && equations()
     */
    public final Formula checkEquations() {
        return decls().and(equations());
    }

    /**
     * Returns the bounds for the problem.
     *
     * @return bounds
     */
    public final Bounds bounds() {
        List<String> atoms = new ArrayList<String>(cols + 1);
        for (int i = 0; i < cols; i++) {
            atoms.add(String.valueOf(i));
        }
        atoms.add("a");
        final Universe u = new Universe(atoms);
        final TupleFactory f = u.factory();
        final Bounds b = new Bounds(u);

        final TupleSet abound = f.setOf("a");
        for (int i = 0; i < rows; i++) {
            for (int j = 0; j < cols; j++) {
                b.bound(a[i][j], abound);
            }
        }
        final TupleSet xbound = f.range(f.tuple(String.valueOf(0)), f.tuple(String.valueOf(cols - 1)));
        for (int j = 0; j < cols; j++) {
            b.bound(x[j], xbound);
            b.boundExactly(j, f.setOf(String.valueOf(j)));
        }

        return b;
    }

    private final void display(Instance instance, Options options) {
        final Evaluator eval = new Evaluator(instance, options);
        for (int i = 0; i < 2; i++) {
            System.out.print("                      | ");
            System.out.print(instance.tuples(x[i]).indexView().min());
            System.out.println(" |");
        }

        for (int i = 0; i < rows; i++) {
            System.out.print("| ");
            for (int j = 0; j < cols; j++) {
                System.out.print(instance.tuples(a[i][j]).isEmpty() ? 0 : 1);
                System.out.print(" ");
            }
            System.out.print(i == 1 ? "| * | " : "|   | ");
            System.out.print(instance.tuples(x[i + 2]).indexView().min());
            System.out.print(i == 1 ? " | = | " : " |   | ");
            System.out.print(eval.evaluate(b[i]));
            System.out.println(" |");
        }

        for (int i = 5; i < 8; i++) {
            System.out.print("                      | ");
            System.out.print(instance.tuples(x[i]).indexView().min());
            System.out.println(" |");
        }

        // for(int i = 0; i < 3; i++)
        // System.out.println(b[i]);
        //
        // for(int i = 0; i < rows; i++) {
        // for(int j = 0 ; j < 8; j++) {
        // IntExpression e0 = x[j].sum();
        // IntExpression e1 = a[i][j].some().thenElse(e0,
        // IntConstant.constant(0));
        // System.out.println(e0 + " : " + eval.evaluate(e0));
        // System.out.println(e1 + " : " + eval.evaluate(e1));
        // }
        // }
    }

    /**
     * Usage: java tests.Viktor
     */
    public static void main(String[] args) {

        final Viktor model = new Viktor();

        final Solver solver = new Solver();
        solver.options().setSolver(SATFactory.MiniSat);
        solver.options().setReporter(new ConsoleReporter());
        solver.options().setBitwidth(7);
        final Formula f = model.checkEquations();
        final Bounds b = model.bounds();
        System.out.println(f);
        System.out.println(b);
        final Solution sol = solver.solve(f, b);

        System.out.println(sol);
        if (sol.instance() != null)
            model.display(sol.instance(), solver.options());

    }

}
