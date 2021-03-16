package kodkod.engine;

import java.util.Iterator;
import java.util.NoSuchElementException;

import kodkod.ast.Formula;
import kodkod.engine.config.Options;
import kodkod.engine.fol2sat.HigherOrderDeclException;
import kodkod.engine.fol2sat.SymmetryDetector;
import kodkod.engine.fol2sat.Translator;
import kodkod.engine.fol2sat.UnboundLeafException;
import kodkod.engine.hol.HOLTranslation;
import kodkod.engine.hol.HOLTranslator;
import kodkod.engine.hol.Proc;
import kodkod.engine.satlab.SATAbortedException;
import kodkod.instance.Bounds;

public final class HOLSolver implements KodkodSolver {

    private final Options  options;
    private HOLTranslation translation;
    private Boolean        outcome;

    private HOLSolver() {
        this(new Options());
    }

    /**
     * Initializes the solver with the given options.
     *
     * @ensures no this.solution' && no this.formulas' && no this.bounds'&&
     *          this.options' = options
     */
    private HOLSolver(Options options) {
        this.options = options;
        this.outcome = null;
    }

    public static HOLSolver solver() {
        return solver(new Options());
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
    public static HOLSolver solver(Options options) {
        Translator.checkIncrementalOptions(options);
        return new HOLSolver(options.clone());
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

        try {
            final long startProcTransl = System.currentTimeMillis();
            Proc proc = Translator.translate2proc(f, b, options);
            final long endProcTransl = System.currentTimeMillis();

            final long startTransl = System.currentTimeMillis();
            translation = HOLTranslator.proc2transl(proc, options);
            final long endTransl = System.currentTimeMillis();

            // final long startTransl = System.currentTimeMillis();
            // translation = Translator.translateHOL(f, b, options);
            // final long endTransl = System.currentTimeMillis();

            return toSolution(endProcTransl - startProcTransl, endTransl - startTransl, translation);
        } catch (SATAbortedException sae) {
            free();
            throw new AbortedException(sae);
        } catch (RuntimeException e) {
            free();
            throw e;
        }
    }

    private Solution toSolution(final long procTranslTime, final long translTime, final HOLTranslation translation) {
        Solution sol = Solver.solveTranslation(translTime, translation);
        sol.stats().setProcTranslTime(procTranslTime);
        sol.stats().setNumCandidates(translation.numCandidates());
        outcome = sol.sat() ? Boolean.TRUE : Boolean.FALSE;
        if (outcome == Boolean.FALSE)
            free();
        return sol;
    }

    public Solution solveNext() {
        HOLTranslation tr = translation.next();
        return toSolution(0, 0, tr);
    }

    @Override
    public Iterator<Solution> solveAll(final Formula formula, final Bounds bounds) throws HigherOrderDeclException, UnboundLeafException, AbortedException {
        return new Iterator<Solution>() {

            private Solution lastSol = null;

            @Override
            public boolean hasNext() {
                return lastSol == null || lastSol.sat();
            }

            @Override
            public Solution next() {
                if (!hasNext())
                    throw new NoSuchElementException();
                lastSol = (lastSol == null) ? solve(formula, bounds) : solveNext();
                return lastSol;
            }

            @Override
            public void remove() {
                throw new IllegalStateException("can't remove solution");
            }
        };
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
        return options;
    }

    /**
     * Releases the resources, if any, associated with this solver.
     */
    @Override
    public void free() {
        if (translation != null) {
            // TODO: translation.cnf().free();
            translation = null;
        }
    }

}
