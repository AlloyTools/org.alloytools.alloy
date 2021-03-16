/*
 * Kodkod -- Copyright (c) 2005-2008, Emina Torlak
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */
package examples.netconfig;

import java.util.ArrayList;
import java.util.List;

import kodkod.ast.Formula;
import kodkod.ast.IntConstant;
import kodkod.ast.IntExpression;
import kodkod.ast.Relation;
import kodkod.engine.Evaluator;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.config.Options;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.Tuple;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

/**
 * A Kodkod encoding of the integer constraint problem for ConfigAssure. It is
 * of the form a1 <= v1 <= a2 <= v2 .... a1000<=v1000 where each vi is a
 * variable and each ai is a constant. The ais are 10 apart, starting at
 * 3232226033 and ending at 3232236033.
 *
 * @author Emina Torlak
 */
public final class IntConstraints {

    private final Relation[] var;
    private final int        low = (int) 3232226033L, high = (int) 3232236033L;

    /**
     * Constructs a new instance of the {@link IntConstraints} problem.
     */
    public IntConstraints() {
        var = new Relation[1000];
        for (int i = 0; i < 1000; i++) {
            var[i] = Relation.unary("var_" + (i + 1));
        }
    }

    /**
     * Returns a bounds for the problem.
     */
    public final Bounds bounds() {
        final List<Integer> atoms = new ArrayList<Integer>(14);
        for (int i = 0; i < 32; i++) {
            atoms.add(Integer.valueOf(1 << i));
        }

        final Universe u = new Universe(atoms);
        final TupleFactory f = u.factory();
        final Bounds b = new Bounds(u);

        // bound the integers
        for (int i = 0; i < 32; i++) {
            b.boundExactly(1 << i, f.setOf(Integer.valueOf(1 << i)));
        }

        // bound the relations, making sure to specify the partial
        // instance based on the low/high range for each variable.
        for (int i = 0; i < 1000; i++) {
            TupleSet lower = f.noneOf(1), upper = f.noneOf(1);
            int min = low + i * 10, max = min + 10, bit = 31;

            // get the common high order bit pattern into lower/upper bound
            // constraints
            while (bit >= 0) {
                int bitVal = 1 << bit;
                if ((min & bitVal) == (max & bitVal)) {
                    if ((min & bitVal) != 0) {
                        Tuple bitTuple = f.tuple(Integer.valueOf(bitVal));
                        lower.add(bitTuple);
                        upper.add(bitTuple);
                    }
                } else {
                    break; // get out of the loop as soon as patterns diverge
                }
                bit--;
            }

            // the bits on which min/max disagree should be variables, so put
            // them into upper bound but not lower
            while (bit >= 0) {
                upper.add(f.tuple(Integer.valueOf(1 << bit)));
                bit--;
            }

            b.bound(var[i], lower, upper);

        }

        return b;
    }

    /**
     * Returns the formula a1 <= v1 <= a2 <= v2 .... a1000<=v1000
     *
     * @return the formula
     */
    public final Formula formula() {
        final List<Formula> constraints = new ArrayList<Formula>(2000);
        final List<IntConstant> constants = new ArrayList<IntConstant>(1001);
        for (int i = low; i <= high; i += 10) {
            constants.add(IntConstant.constant(i));
        }

        for (int i = 0; i < 1000; i++) {
            IntExpression varExpr = var[i].sum(); // convert to primitive int
            constraints.add(constants.get(i).lte(varExpr)); // a_i <= v_i
            constraints.add(varExpr.lte(constants.get(i + 1))); // v_i <=
                                                               // a_(i+1)
        }

        return Formula.and(constraints);
    }

    /**
     * Prints the solution to the screen.
     */
    private final void print(Solution sol, Options options) {
        System.out.println(sol.stats());
        final Evaluator eval = new Evaluator(sol.instance(), options);
        final long mask = -1L >>> 32;
        for (int i = 0; i < 1000; i++) {
            long min = (low + 10 * i) & mask, max = (min + 10) & mask;
            long result = eval.evaluate(var[i].sum()) & mask;
            System.out.println(min + " <= [var_" + (i + 1) + "=" + result + "] <= " + max);
        }
    }

    /**
     * Usage: java examples.IntConstraints
     */
    public static void main(String[] args) {
        final IntConstraints model = new IntConstraints();
        final Bounds bounds = model.bounds();
        final Formula formula = model.formula();

        final Solver solver = new Solver();
        solver.options().setBitwidth(32);
        solver.options().setSolver(SATFactory.MiniSat);

        final Solution sol = solver.solve(formula, bounds);
        model.print(sol, solver.options());

    }

}
