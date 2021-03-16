package kodkod.engine;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.NoSuchElementException;

import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.config.Options;
import kodkod.engine.fol2sat.Translation;
import kodkod.engine.fol2sat.Translator;
import kodkod.engine.satlab.SATAbortedException;
import kodkod.engine.satlab.SATSolver;
import kodkod.instance.Bounds;
import kodkod.instance.TupleSet;

/**
 * An iterator over all solutions of a model.
 *
 * @author Emina Torlak
 */
public final class SolutionIterator implements Iterator<Solution> {

    private Translation.Whole translation;
    private long              translTime;
    private int               trivial;

    /**
     * Constructs a solution iterator for the given formula, bounds, and options.
     */
    SolutionIterator(Formula formula, Bounds bounds, Options options) {
        this.translTime = System.currentTimeMillis();
        this.translation = Translator.translate(formula, bounds, options);
        this.translTime = System.currentTimeMillis() - translTime;
        this.trivial = 0;
    }

    /**
     * Returns true if there is another solution.
     *
     * @see java.util.Iterator#hasNext()
     */
    @Override
    public boolean hasNext() {
        return translation != null;
    }

    /**
     * Returns the next solution if any.
     *
     * @see java.util.Iterator#next()
     */
    @Override
    public Solution next() {
        if (!hasNext())
            throw new NoSuchElementException();
        try {
            return translation.trivial() ? nextTrivialSolution() : nextNonTrivialSolution();
        } catch (SATAbortedException sae) {
            translation.cnf().free();
            throw new AbortedException(sae);
        }
    }

    /** @throws UnsupportedOperationException */
    @Override
    public void remove() {
        throw new UnsupportedOperationException();
    }

    /**
     * Solves {@code translation.cnf} and adds the negation of the found model to
     * the set of clauses. The latter has the effect of forcing the solver to come
     * up with the next solution or return UNSAT. If
     * {@code this.translation.cnf.solve()} is false, sets {@code this.translation}
     * to null.
     *
     * @requires this.translation != null
     * @ensures this.translation.cnf is modified to eliminate the current solution
     *          from the set of possible solutions
     * @return current solution
     */
    private Solution nextNonTrivialSolution() {
        final Translation.Whole transl = translation;

        final SATSolver cnf = transl.cnf();
        final int primaryVars = transl.numPrimaryVariables();

        transl.options().reporter().solvingCNF(primaryVars, cnf.numberOfVariables(), cnf.numberOfClauses());

        final long startSolve = System.currentTimeMillis();
        final boolean isSat = cnf.solve();
        final long endSolve = System.currentTimeMillis();

        final Statistics stats = new Statistics(transl, translTime, endSolve - startSolve);
        final Solution sol;

        if (isSat) {
            // extract the current solution; can't use the sat(..) method
            // because it frees the sat solver
            sol = Solution.satisfiable(stats, transl.interpret());
            // add the negation of the current model to the solver
            final int[] notModel = new int[primaryVars];
            for (int i = 1; i <= primaryVars; i++) {
                notModel[i - 1] = cnf.valueOf(i) ? -i : i;
            }
            cnf.addClause(notModel);
        } else {
            sol = Solver.unsat(transl, stats); // this also frees up solver
                                              // resources, if any
            translation = null; // unsat, no more solutions
        }
        return sol;
    }

    /**
     * Returns the trivial solution corresponding to the trivial translation stored
     * in {@code this.translation}, and if {@code this.translation.cnf.solve()} is
     * true, sets {@code this.translation} to a new translation that eliminates the
     * current trivial solution from the set of possible solutions. The latter has
     * the effect of forcing either the translator or the solver to come up with the
     * next solution or return UNSAT. If {@code this.translation.cnf.solve()} is
     * false, sets {@code this.translation} to null.
     *
     * @requires this.translation != null
     * @ensures this.translation is modified to eliminate the current trivial
     *          solution from the set of possible solutions
     * @return current solution
     */
    private Solution nextTrivialSolution() {
        final Translation.Whole transl = this.translation;

        final Solution sol = Solver.trivial(transl, translTime); // this also
                                                                // frees up
                                                                // solver
                                                                // resources,
                                                                // if unsat

        if (sol.instance() == null) {
            translation = null; // unsat, no more solutions
        } else {
            trivial++;

            final Bounds bounds = transl.bounds();
            final Bounds newBounds = bounds.clone();
            final List<Formula> changes = new ArrayList<Formula>();

            for (Relation r : bounds.relations()) {
                final TupleSet lower = bounds.lowerBound(r);

                if (lower != bounds.upperBound(r)) { // r may change
                    if (lower.isEmpty()) {
                        changes.add(r.some());
                    } else {
                        final Relation rmodel = Relation.nary(r.name() + "_" + trivial, r.arity());
                        newBounds.boundExactly(rmodel, lower);
                        changes.add(r.eq(rmodel).not());
                    }
                }
            }

            // nothing can change => there can be no more solutions (besides the
            // current trivial one).
            // note that transl.formula simplifies to the constant true with
            // respect to
            // transl.bounds, and that newBounds is a superset of transl.bounds.
            // as a result, finding the next instance, if any, for
            // transl.formula.and(Formula.or(changes))
            // with respect to newBounds is equivalent to finding the next
            // instance of Formula.or(changes) alone.
            final Formula formula = changes.isEmpty() ? Formula.FALSE : Formula.or(changes);

            final long startTransl = System.currentTimeMillis();
            translation = Translator.translate(formula, newBounds, transl.options());
            translTime += System.currentTimeMillis() - startTransl;
        }
        return sol;
    }

}
