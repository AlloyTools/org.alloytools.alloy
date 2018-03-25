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
import kodkod.engine.config.Options;
import kodkod.engine.fol2sat.HigherOrderDeclException;
import kodkod.engine.fol2sat.SymmetryDetector;
import kodkod.engine.fol2sat.Translation;
import kodkod.engine.fol2sat.Translator;
import kodkod.engine.fol2sat.UnboundLeafException;
import kodkod.engine.satlab.SATAbortedException;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.satlab.SATSolver;
import kodkod.instance.Bounds;
import kodkod.instance.Universe;

/**
 * A computational engine for solving a sequence of related relational
 * {@linkplain Formula formulas} and {@linkplain Bounds bounds} (e.g., generated
 * by a software verification or synthesis tool) with respect to a given set of
 * configuration {@link kodkod.engine.config.Options options}.
 * <p>
 * An incremental Kodkod solver is initialized with an options instance
 * <code>opt</code> which cannot be modified further during the lifetime of the
 * solver instance. If the first problem <code>(f0, b0, opt)</code> passed to
 * the solver via the {@link #solve(Formula, Bounds) solve} method is
 * satisfiable, the resulting {@linkplain Solution solution} and the underlying
 * incremental {@linkplain SATSolver SAT solver} are saved. When the
 * {@linkplain #solve(Formula, Bounds) solve} method is called again with a new
 * formula <code>f1</code> and bounds <code>b1</code>, the translation of
 * <code>(f1, b1, opt)</code> is added to the stored SAT solver, which is then
 * called to obtain a solution for the problem <code>f0 && f1</code> and
 * <code>b0 + b1</code>. We define <code>b0 + b1</code> to be a disjoint union
 * of the bindings in <code>b0</code> and <code>b1</code>, where
 * {@code b0.universe = b1.universe}, {@code b1.intBound} is empty, and
 * {@code b1} contains no bindings for relations that are bound by {@code b0}.
 * This process can be repeated until the solver yields UNSAT. Calling
 * {@linkplain #solve(Formula, Bounds) solve} on a solver that has already
 * returned UNSAT or that has thrown an exception during a prior call to
 * {@linkplain #solve(Formula, Bounds) solve} will result in an
 * {@link IllegalStateException}.
 * </p>
 * <p>
 * To simplify the implementation, an {@linkplain IncrementalSolver} currently
 * places the following restriction on the sequence of bounds passed to its
 * {@linkplain #solve(Formula, Bounds)} method: the equivalence classes on the
 * {@linkplain Universe universe} of interpretation that are induced by the
 * initial bounds <code>b0</code> must refine the equivalence classes induced by
 * all subsequent bounds. In particular, let <code>{ s0, ..., sn }</code> be the
 * coarsest partition of <code>b0.universe</code> such that every tupleset in
 * <code>b0.lowerBound</code>, <code>b0.upperBound</code>, and
 * <code>b0.intBound</code> can be expressed as a union of cross-products of
 * sets drawn from <code>{ s0, ..., sn }</code>. Then, for each bound
 * <code>bi</code> with which the solver's {@linkplain #solve(Formula, Bounds)
 * solve} method is called in the future, it must also be the case that each
 * tupleset in <code>bi.lowerBound</code>, <code>bi.upperBound</code> and
 * <code>bi.intBound</code> can be expressed in the same way, as a union of
 * cross-products of sets drawn from <code>{ s0, ..., sn }</code>.
 * </p>
 * <p>
 * The above requirement can be satisfied by making sure that <code>b0</code>
 * contains a set of unary relations <code>{ r0, ..., rn }</code> such that the
 * lower/upper bounds on all other relations that will ever be introduced can be
 * expressed as a union of cross-products of a subset of <code>b0</code>'s
 * lower/upper bounds on <code>{ r0, ..., rn }</code>. One can think of the
 * bounds on <code>{ r0, ..., rn }</code> as representing sorts or types, and
 * every relation's bounds should be expressible in terms of these types. Note
 * that having each atom in the universe appear in a lower/upper bound by itself
 * (e.g., <code>b0.lowerBound[ri] = b0.upperBound[ri] = {&lt;ai&gt;}</code>)
 * will trivially satisfy this requirement, but it is better to group related
 * atoms into sets to enable symmetry breaking.
 * </p>
 * <p>
 * We additionally require {@linkplain Options#logTranslation()
 * opt.logTranslation} to be {@linkplain Options#setLogTranslation(int)
 * disabled} and {@linkplain Options#solver() opt.solver} to specify an
 * {@linkplain SATFactory#incremental() incremental} SAT solver. Note that these
 * restrictions prevent unsat core extraction.
 * </p>
 *
 * @specfield options: {@link Options}
 * @specfield bounds: lone {@link Bounds}
 * @specfield formulas: set {@link Formula}
 * @invariant formulas.*components & Relation in bounds.relations
 * @invariant some formulas iff some bounds
 * @invariant options.solver.incremental() && options.logTranslation = 0
 * @see SymmetryDetector
 * @see kodkod.engine.fol2sat.Translation.Incremental
 * @see Translator#translateIncremental(Formula, Bounds, Options)
 * @see Translator#translateIncremental(Formula, Bounds,
 *      kodkod.engine.fol2sat.Translation.Incremental)
 * @author Emina Torlak
 */
public final class IncrementalSolver implements KodkodSolver {

    private final Options           options;
    private Translation.Incremental translation;
    private Boolean                 outcome;

    /**
     * Initializes the solver with the given options.
     *
     * @ensures no this.solution' && no this.formulas' && no this.bounds'&&
     *          this.options' = options
     */
    private IncrementalSolver(Options options) {
        this.options = options;
        this.outcome = null;
    }

    /**
     * Returns a new {@link IncrementalSolver} using the given options.
     *
     * @requires options.solver.incremental() && options.logTranslation = 0
     * @return some s: IncrementalSolver | no s.formulas && no s.bounds && s.options
     *         = options.clone()
     * @throws NullPointerException any of the arguments are null
     * @throws IllegalArgumentException any of the preconditions on options are
     *             violated
     */
    public static IncrementalSolver solver(Options options) {
        Translator.checkIncrementalOptions(options);
        return new IncrementalSolver(options.clone());
    }

    /**
     * Adds the specified formula and bounds to the solver's state, modifies the
     * current solution to reflect the updated state (if needed), and returns this
     * solver. This solver should not be used again if a call to this method results
     * in an exception.
     *
     * @requires this.{@link #usable() usable}()
     * @requires f.*components & Relation in (this.bounds + b).relations
     * @requires some this.bounds => this.bounds.universe = b.universe && no
     *           b.intBound && no (this.bounds.relations & b.relations)
     * @requires some this.bounds => all s:
     *           {@link SymmetryDetector#partition(Bounds) partition}(this.bounds) |
     *           some p: {@link SymmetryDetector#partition(Bounds) partition}(b) |
     *           s.elements in p.elements
     * @ensures this.formulas' = this.formulas + f
     * @ensures some this.bounds => (this.bounds.relations' = this.bounds.relations
     *          + b.relations && this.bounds.upperBound' = this.bounds.upperBound +
     *          b.upperBound && this.bounds.lowerBound' = this.bounds.lowerBound +
     *          b.lowerBound) else (this.bounds' = bounds)
     * @return some sol: Solution | sol.instance() = null => UNSAT(this.formulas',
     *         this.bounds', this.options) else sol.instance() in
     *         MODELS(Formula.and(this.formulas'), this.bounds', this.options)
     * @throws IllegalStateException a prior call returned an UNSAT solution or
     *             resulted in an exception
     * @throws NullPointerException any of the arguments are null
     * @throws UnboundLeafException the formula refers to an undeclared variable or
     *             a relation not mapped by this.bounds + b
     * @throws HigherOrderDeclException the formula contains a higher order
     *             declaration
     * @throws IllegalArgumentException any of the remaining preconditions on
     *             {@code f} and {@code b} are violated
     * @throws AbortedException this solving task has been aborted
     */
    @Override
    public Solution solve(Formula f, Bounds b) throws HigherOrderDeclException, UnboundLeafException, AbortedException {
        if (outcome == Boolean.FALSE)
            throw new IllegalStateException("Cannot use this solver since a prior call to solve(...) produced an UNSAT solution.");

        if (outcome != null && translation == null)
            throw new IllegalStateException("Cannot use this solver since a prior call to solve(...) resulted in an exception.");

        final Solution solution;
        try {
            final long startTransl = System.currentTimeMillis();
            translation = translation == null ? Translator.translateIncremental(f, b, options) : Translator.translateIncremental(f, b, translation);
            final long endTransl = System.currentTimeMillis();

            if (translation.trivial()) {
                final Statistics stats = new Statistics(translation, endTransl - startTransl, 0);
                if (translation.cnf().solve()) {
                    solution = Solution.triviallySatisfiable(stats, translation.interpret());
                } else {
                    solution = Solution.triviallyUnsatisfiable(stats, null);
                }
            } else {
                final SATSolver cnf = translation.cnf();

                translation.options().reporter().solvingCNF(translation.numPrimaryVariables(), cnf.numberOfVariables(), cnf.numberOfClauses());
                final long startSolve = System.currentTimeMillis();
                final boolean sat = cnf.solve();
                final long endSolve = System.currentTimeMillis();

                final Statistics stats = new Statistics(translation, endTransl - startTransl, endSolve - startSolve);
                if (sat) {
                    solution = Solution.satisfiable(stats, translation.interpret());
                } else {
                    solution = Solution.unsatisfiable(stats, null);
                }
            }
        } catch (SATAbortedException sae) {
            free();
            throw new AbortedException(sae);
        } catch (RuntimeException e) {
            free();
            throw e;
        }

        if (solution.sat()) {
            outcome = Boolean.TRUE;
        } else {
            outcome = Boolean.FALSE;
            free();
        }

        return solution;
    }

    @Override
    public Iterator<Solution> solveAll(Formula formula, Bounds bounds) throws HigherOrderDeclException, UnboundLeafException, AbortedException {
        throw new RuntimeException("not implemented");
    }

    /**
     * Returns true iff this solver has neither returned an UNSAT solution so far
     * nor thrown an exception during solving.
     *
     * @return true iff this solver has neither returned an UNSAT solution so far
     *         nor thrown an exception during solving
     */
    public boolean usable() {
        return (outcome == Boolean.TRUE && translation != null) || (outcome == null);
    }

    /**
     * Returns a copy of {@code this.options}.
     *
     * @return this.options.clone()
     */
    @Override
    public Options options() {
        return options.clone();
    }

    /**
     * Releases the resources, if any, associated with this solver.
     */
    @Override
    public void free() {
        if (translation != null) {
            translation.cnf().free();
            translation = null;
        }
    }

}
