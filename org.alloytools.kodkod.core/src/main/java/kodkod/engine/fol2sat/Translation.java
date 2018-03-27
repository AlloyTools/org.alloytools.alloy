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
package kodkod.engine.fol2sat;

import java.util.Map;
import java.util.Set;

import kodkod.ast.Relation;
import kodkod.engine.bool.BooleanConstant;
import kodkod.engine.config.Options;
import kodkod.engine.satlab.SATSolver;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.util.ints.IndexedEntry;
import kodkod.util.ints.IntIterator;
import kodkod.util.ints.IntSet;
import kodkod.util.ints.Ints;

/**
 * Stores the translation of a Kodkod problem to CNF. A problem consists of a
 * {@linkplain kodkod.ast.Formula formula}, {@linkplain Bounds bounds} and
 * {@linkplain Options}. A translation can be {@linkplain Whole basic} or
 * {@linkplain Incremental incremental}.
 *
 * @specfield originalFormula: Formula // the original formula, as constructed
 *            by client
 * @specfield originalBounds: Bounds // the original bounds, as constructed by
 *            client
 * @specfield formula: Formula // optimization of this.originalFormula that was
 *            used for translation
 * @specfield bounds: Bounds // optimization of this.originalBounds that was
 *            used for translation
 * @specfield options: Options // the options object used to control translation
 * @specfield vars: this.bounds.relations -> int // mapping from relations to
 *            variables that encode their contents
 * @specfield solver: SATSolver // a SATSolver containing the CNF representation
 *            of the formula
 * @invariant solver.solve() iff SAT(formula, bounds, options)
 * @invariant SAT(formula, bounds, options) iff SAT(originalFormula,
 *            originalBounds, options)
 * @invariant this.originalBounds.relations in this.bounds.relations
 * @invariant this.originalBounds.ints().equals(this.bounds.ints())
 * @invariant all r: this.bounds.relations | some vars[r] => #vars[r] =
 *            this.bounds.upperBound(r).size() -
 *            this.bounds.lowerBound(r).size()
 * @invariant all r: this.bounds.relations, i: vars[r] | min(vars[r]) <= i <=
 *            max(vars[r])
 * @invariant vars[Relation] in this.solver.variables
 * @see Whole
 * @see Incremental
 * @author Emina Torlak
 */
public abstract class Translation {

    protected final Bounds  bounds;
    protected final Options options;

    /**
     * Creates a translation using the given bounds and options.
     *
     * @ensures this.bounds' = bounds && this.options' = options
     */
    protected Translation(Bounds bounds, Options options) {
        this.bounds = bounds;
        this.options = options;
    }

    /**
     * Returns the optimized bounds. Modification of the returned object may cause
     * violation of {@link Translation} invariants.
     *
     * @return this.bounds
     */
    public final Bounds bounds() {
        return bounds;
    }

    /**
     * Returns the translation options. Modification of the returned object may
     * cause violation of {@link Translation} invariants.
     *
     * @return this.options
     */
    public final Options options() {
        return options;
    }

    /**
     * Returns the set of primary variables that represent the tuples in the given
     * relation. If no variables were allocated to the given relation, empty set is
     * returned. This set contains exactly
     * {@code this.bounds.upperBound(r).size() - this.bounds.lowerBound(r).size()}
     * variable identifiers.
     *
     * @return this.vars[relation]
     */
    public abstract IntSet primaryVariables(Relation relation);

    /**
     * Returns the number of primary variables allocated during translation. Primary
     * variables represent the tuples of relations in this.bounds that have
     * different lower and upper bounds (i.e.
     * {@code some this.bounds.upperBound[r].tuples - this.bounds.lowerBound[r].tuples}).
     *
     * @return #this.vars[Relation]
     */
    public abstract int numPrimaryVariables();

    /**
     * Returns the SATSolver object containing the CNF encoding of this.formula.
     * Satisfiability of the formula can be checked by calling
     * {@link kodkod.engine.satlab.SATSolver#solve()}. Modification of the returned
     * object may cause violation of {@link Translation} invariants.
     *
     * @return {s: SATSolver | SAT(s.variables, s.clauses) iff SAT(this.formula,
     *         this.bounds, this.options) }
     */
    public abstract SATSolver cnf();

    /**
     * Returns true iff this translation is trivially true or trivially false. We
     * consider a problem defined by {@code this.formula} and {@code this.bounds} to
     * be trivially true or false if the {@linkplain Translator} simplifies it to a
     * {@linkplain BooleanConstant}. The {@linkplain BooleanConstant#TRUE TRUE}
     * value is represented as a {@linkplain #cnf() CNF} with no variables and no
     * clauses. The {@linkplain BooleanConstant#FALSE FALSE} value is represented as
     * a {@linkplain #cnf() CNF} with no variables and a single, empty clause. Note
     * that in the case of a trivially satisfiable problem, the {@link #interpret()}
     * method returns the minimal trivial instance for that problem, which consists
     * of the lower bounds specified by {@code this.bounds}.
     *
     * @return this.cnf.numberOfVariables() = 0
     * @see #interpret()
     */
    public boolean trivial() {
        return cnf().numberOfVariables() == 0;
    }

    /**
     * If {@code this.solver.solve()} is true, returns an interpretation of the CNF
     * solution as a mapping from Relations to sets of Tuples. The returned instance
     * maps all relations in {@code this.bounds} and, therefore, all relations in
     * {@code this.originalBounds}. The additional relations in {@code this.bounds},
     * if any, consist of generated skolem constants.
     * <p>
     * The returned {@code instance} assigns the value {@code instance.tuples(r)} to
     * each relation {@code r} in {@code this.bounds.relations} as follows: (1)
     * {@code instance.tuples(r)} includes all tuples in
     * {@code this.bound.lowerBound(r)}, and (2) it includes the ith tuple from
     * {@code this.bounds.upperBound(r) - this.bounds.lowerBound(r)} iff the model
     * obtain from {@code this.solver} binds the ith variable in
     * {@code this.{@linkplain #primaryVariables(Relation) primaryVariables}(r)} to
     * true. In other words, if no primary variables were allocated to {@code r},
     * then the returned instance simply binds {@code r} to its lower bound. Note
     * that in the case of a trivially satisfiable problem
     * {@code (this.formula, this.bounds, this.options)}, the returned
     * {@code instance} is the smallest possible instance for that problem,
     * consisting solely of the lower bounds specified by {@code this.bounds}.
     * </p>
     *
     * @return a new instance of the problem
     *         {@code (this.formula, this.bounds, this.options)}, as described above
     * @throws IllegalStateException this.solver.solve() has not been called or the
     *             outcome of the last call was not <code>true</code>.
     */
    public Instance interpret() {
        return interpret(bounds);
    }

    public Instance interpret(Bounds bounds) {
        final SATSolver solver = cnf();
        final Instance instance = new Instance(bounds.universe());
        final TupleFactory f = bounds.universe().factory();
        for (IndexedEntry<TupleSet> entry : bounds.intBounds()) {
            instance.add(entry.index(), entry.value());
        }
        for (Relation r : bounds.relations()) {
            // if (bnds != bounds && bnds.findRelByName(r.name()) == null)
            // continue;
            TupleSet lower = bounds.lowerBound(r);
            IntSet indices = Ints.bestSet(lower.capacity());
            indices.addAll(lower.indexView());
            IntSet vars = primaryVariables(r);
            if (!vars.isEmpty()) {
                // System.out.println(r + ": [" + vars.min() + ", " + vars.max()
                // + "]");
                int lit = vars.min();
                for (IntIterator iter = bounds.upperBound(r).indexView().iterator(); iter.hasNext();) {
                    final int index = iter.next();
                    if (!indices.contains(index) && solver.valueOf(lit++))
                        indices.add(index);
                }
            }
            instance.add(r, f.setOf(r.arity(), indices));
        }
        return instance;
    }

    /**
     * A {@linkplain Whole whole} translation stores the complete CNF of encoding of
     * a given problem. Unlike an {@link Incremental incremental} translation, a
     * whole translation cannot be augmented with additional constraints. The
     * tradeoff is that a whole translation is cheaper to store; the encoding may be
     * more efficient than if the same problem were translated incrementally; and,
     * whole translations support logging and core extraction
     *
     * @specfield log: lone {@link TranslationLog} // a translation log mapping
     *            nodes in this.formula to their corresponding literals in
     *            this.solver
     * @invariant some log => log.originalFormula = originalFormula &&
     *            log.originalBounds = originalBounds && log.formula = formula &&
     *            log.bounds = bounds
     * @invariant some log iff this.options.logTranslation > 0
     * @invariant vars[this.bounds.relations] = { i: int | 1 <= i <= #vars }
     * @see Translator#translate(kodkod.ast.Formula, Bounds, Options)
     * @author Emina Torlak
     */
    public static final class Whole extends Translation {

        private final SATSolver            solver;
        private final Map<Relation,IntSet> primaryVarUsage;
        private final TranslationLog       log;
        private final int                  maxPrimaryVar;

        /**
         * Creates a whole translation using the given bounds, options, solver, var map,
         * and log.
         *
         * @requires primaryVarUsage.keySet() in { r: bounds.relations | bounds.lower[r]
         *           != bounds.upper[r] }
         * @requires maxPrimaryVar = max(varUsage[Relation].max)
         * @requires all i: varUsage.map[Relation].ints | 1 <= i <= maxPrimaryVar
         * @requires varUsage.map[Relation].ints in solver.variables
         * @ensures this.solver' = solver && this.bounds' = bounds && this.options' =
         *          options && this.log' = log && this.vars' = varUsage
         */
        Whole(Bounds bounds, Options options, SATSolver solver, Map<Relation,IntSet> varUsage, int maxPrimaryVar, TranslationLog log) {
            super(bounds, options);
            this.solver = solver;
            this.log = log;
            this.maxPrimaryVar = maxPrimaryVar;
            this.primaryVarUsage = varUsage;
        }

        /**
         * {@inheritDoc}
         *
         * @see kodkod.engine.fol2sat.Translation#cnf()
         */
        @Override
        public final SATSolver cnf() {
            return solver;
        }

        /**
         * {@inheritDoc}
         *
         * @see kodkod.engine.fol2sat.Translation#primaryVariables(kodkod.ast.Relation)
         */
        @Override
        public IntSet primaryVariables(Relation relation) {
            final IntSet vars = primaryVarUsage.get(relation);
            return vars == null ? Ints.EMPTY_SET : vars;
        }

        /**
         * {@inheritDoc}
         *
         * @see kodkod.engine.fol2sat.Translation#numPrimaryVariables()
         */
        @Override
        public int numPrimaryVariables() {
            return maxPrimaryVar;
        }

        /**
         * If translation logging was enabled (by setting
         * {@code this.options.logTranslation > 0}), returns the
         * {@linkplain TranslationLog log} of {@linkplain TranslationRecord records}
         * generated for this translation. Otherwise returns null.
         *
         * @return translation log for this translation, if one was generated, or null
         *         otherwise
         */
        public TranslationLog log() {
            return log;
        }
    }

    /**
     * An {@linkplain Incremental incremental} translation preserves the internal
     * data structures used during translation. This enables the translation to be
     * updated with CNF encodings of additional formulas and bounds using the
     * {@linkplain Translator#translateIncremental(kodkod.ast.Formula, Bounds, Translation.Incremental)}
     * method.
     * <p>
     * Incremental translations are more expensive to store than {@link Whole whole}
     * translations, and they place some restrictions on the form of problems that
     * are translated. In particular, logging must be disabled during translation;
     * the translation must use an incremental SAT solver; and the addition of new
     * clauses must not violate the invariants guaranteed by the {@link Translation}
     * class. All three restrictions are enforced by the
     * {@code translateIncremental(...)} methods of the {@link Translator} class.
     * </p>
     *
     * @specfield symmetries: set IntSet // partition of the universe into
     *            equivalence classes induced this.originalBounds
     * @invariant this.options.logTranslation = 0 &&
     *            this.options.solver.incremental()
     * @invariant this.symmetries = {@linkplain SymmetryDetector#partition(Bounds)
     *            partition}(this.originalBounds)
     * @see Translator#translateIncremental(kodkod.ast.Formula, Bounds, Options)
     * @see Translator#translateIncremental(kodkod.ast.Formula, Bounds,
     *      Translation.Incremental)
     * @author Emina Torlak
     */
    public static final class Incremental extends Translation {

        /**
         * @invariant this.interpreter.universe = this.bounds.universe &&
         *            this.interpreter.relations in this.bounds.relations &&
         *            this.interpreter.intBound = this.bounds.ibounds &&
         *            this.interpreter.lowerBound in this.bounds.lbounds &&
         *            this.interpreter.upperBound in this.bounds.ubounds &&
         *            this.interpreter.vars = this.vars.label
         **/
        private final LeafInterpreter    interpreter;
        /**
         * @invariant this.incrementer.solver = this.solver
         * @invariant this.incrementer.factory = this.interpreter.factory
         */
        private final Bool2CNFTranslator incrementer;
        private final Set<IntSet>        symmetries;

        /**
         * Creates an Incremental translation using the given bounds, options,
         * symmetries of the original bounds, translator and interpreter. This
         * constructor assumes that the symmetries induced by {@code bounds} refine the
         * {@code originalSymmetries}, which were obtained from the original problem
         * bounds.
         *
         * @requires options.logTranslation = 0 && options.solver.incremental()
         * @requires translator.solver was constructed by calling
         *           options.solver.instance()
         * @requires all s : SymmetryDetector.partition(bounds) | some p :
         *           originalSymmetries | s.ints in p.ints
         * @ensures this.bounds' = bounds && this.options' = options && this.symmetries'
         *          = originalSymmetries && this.incrementer' = incrementer &&
         *          this.interpreter' = interpreter
         */
        Incremental(Bounds bounds, Options options, Set<IntSet> originalSymmetries, LeafInterpreter interpreter, Bool2CNFTranslator translator) {
            super(bounds, options);
            this.interpreter = interpreter;
            this.incrementer = translator;
            this.symmetries = originalSymmetries;
        }

        /**
         * Returns the symmetries induced by the original bounds.
         *
         * @return this.symmetries
         */
        Set<IntSet> symmetries() {
            return symmetries;
        }

        /**
         * Returns this.interpreter.
         *
         * @return this.interpreter
         */
        LeafInterpreter interpreter() {
            return interpreter;
        }

        /**
         * Returns this.incrementer.
         *
         * @return this.incrementer.
         */
        Bool2CNFTranslator incrementer() {
            return incrementer;
        }

        /**
         * {@inheritDoc}
         *
         * @see kodkod.engine.fol2sat.Translation#cnf()
         */
        @Override
        public final SATSolver cnf() {
            return incrementer.solver();
        }

        /**
         * {@inheritDoc}
         *
         * @see kodkod.engine.fol2sat.Translation#primaryVariables(kodkod.ast.Relation)
         */
        @Override
        public IntSet primaryVariables(Relation relation) {
            return interpreter.vars(relation);
        }

        /**
         * {@inheritDoc}
         *
         * @see kodkod.engine.fol2sat.Translation#numPrimaryVariables()
         */
        @Override
        public int numPrimaryVariables() {
            return interpreter.factory().numberOfVariables();
        }

    }

}
