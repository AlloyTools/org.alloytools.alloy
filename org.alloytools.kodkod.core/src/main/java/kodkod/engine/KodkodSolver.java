/*
 * Kodkod -- Copyright (c) 2005-2012, Emina Torlak
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
package kodkod.engine;

import java.util.Iterator;

import kodkod.ast.Formula;
import kodkod.ast.IntExpression;
import kodkod.ast.Relation;
import kodkod.engine.config.Options;
import kodkod.engine.fol2sat.HigherOrderDeclException;
import kodkod.engine.fol2sat.UnboundLeafException;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;

/**
 * A computational engine for solving relational satisfiability problems. Such a
 * problem is described by a {@link kodkod.ast.Formula formula} in first order
 * relational logic; finite {@link kodkod.instance.Bounds bounds} on the value
 * of each {@link Relation relation} constrained by the formula; and a set of
 * {@link kodkod.engine.config.Options options} specifying, among other global
 * parameters, the length of bitvectors that describe the meaning of
 * {@link IntExpression integer expressions} in the given formula. The options
 * are usually reused between invocations to the
 * {@linkplain #solve(Formula, Bounds) solve} methods, so they are specified as
 * a part of the {@linkplain KodkodSolver solver} state.
 * <p>
 * A {@link KodkodSolver} takes as input a relational problem and produces a
 * satisfying model or an {@link Instance instance} of it, if one exists. Some
 * implementation of this interface can also produce a {@link Proof proof} of
 * unsatisfiability, if the given problem has no models.
 * </p>
 *
 * @specfield options: Options
 * @author Emina Torlak
 */
public interface KodkodSolver {

    /**
     * Returns the Options object used by this solver.
     *
     * @return this.options
     */
    public Options options();

    /**
     * Attempts to satisfy the given {@code formula} and {@code bounds} with respect
     * to {@code this.options} or, optionally, prove the problem's unsatisfiability.
     * If the method completes normally, the result is a {@linkplain Solution
     * solution} containing either an {@linkplain Instance instance} of the given
     * problem or, optionally, a {@linkplain Proof proof} of its unsatisfiability.
     *
     * @return some sol: {@link Solution} | sol.satisfiable() => sol.instance() in
     *         MODELS(formula, bounds, this.options) else UNSAT(formula, bound,
     *         this.options)
     * @throws NullPointerException formula = null || bounds = null
     * @throws UnboundLeafException the formula contains an undeclared variable or a
     *             relation not mapped by the given bounds
     * @throws HigherOrderDeclException the formula contains a higher order
     *             declaration that cannot be skolemized, or it can be skolemized
     *             but {@code this.options.skolemDepth} is insufficiently large
     * @throws AbortedException this solving task was aborted
     */
    public Solution solve(Formula formula, Bounds bounds) throws HigherOrderDeclException, UnboundLeafException, AbortedException;

    public Iterator<Solution> solveAll(Formula fgoal, Bounds bounds) throws HigherOrderDeclException, UnboundLeafException, AbortedException;;

    // /**
    // * Attempts to find a set of solutions to the given {@code formula} and
    // {@code bounds} with respect to
    // * {@code this.options} or, optionally, to prove the formula's
    // unsatisfiability.
    // * If the operation is successful, the method returns an iterator over
    // {@link Solution} objects.
    // * If there is more than one solution, the outcome of all of them is SAT
    // or trivially SAT. If the problem
    // * is unsatisfiable, the iterator will produce a single {@link Solution}
    // whose outcome is UNSAT
    // * or trivially UNSAT. The set of returned solutions must be non-empty,
    // but it is not required to be complete;
    // * a solver could simply return a singleton set containing just the first
    // available solution.
    // *
    // * @return some sols: some {@link Solution} |
    // * (#sols > 1 => (all s: sols | s.satisfiable())) &&
    // * (all s: sols | s.satisfiable() => s.instance() in MODELS(formula,
    // bounds, this.options) else UNSAT(formula, bound, this.options))
    // *
    // * @throws NullPointerException formula = null || bounds = null
    // * @throws UnboundLeafException the formula contains an undeclared
    // variable or a relation not mapped by the given bounds
    // * @throws HigherOrderDeclException the formula contains a higher order
    // declaration that cannot
    // * be skolemized, or it can be skolemized but {@code
    // this.options.skolemDepth} is insufficiently large
    // * @throws AbortedException this solving task was aborted
    // */
    // public Iterator<Solution> solveAll(Formula formula, Bounds bounds)
    // throws HigherOrderDeclException, UnboundLeafException, AbortedException;

    /**
     * Releases the resources, if any, associated with this solver.
     */
    public void free();

}
