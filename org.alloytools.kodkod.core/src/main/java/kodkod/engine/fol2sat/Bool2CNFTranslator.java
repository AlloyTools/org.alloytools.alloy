/*
 * Kodkod -- Copyright (c) 2005-present, Emina Torlak
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

import static kodkod.engine.bool.Operator.AND;

import kodkod.engine.bool.BooleanConstant;
import kodkod.engine.bool.BooleanFactory;
import kodkod.engine.bool.BooleanFormula;
import kodkod.engine.bool.BooleanVariable;
import kodkod.engine.bool.BooleanVisitor;
import kodkod.engine.bool.ITEGate;
import kodkod.engine.bool.MultiGate;
import kodkod.engine.bool.NotGate;
import kodkod.engine.bool.Operator;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.satlab.SATSolver;
import kodkod.util.ints.IntSet;
import kodkod.util.ints.IntTreeSet;

/**
 * Transforms a boolean circuit into a formula in conjunctive normal form.
 *
 * @specfield factory: {@link BooleanFactory}
 * @specfield roots: some factory.components
 * @specfield cnf: {@link SATSolver}
 * @invariant max(abs(roots.label)) = max(cnf.variables)
 * @invariant meaning(roots) = meaning(cnf.clauses)
 * @author Emina Torlak
 */
abstract class Bool2CNFTranslator implements BooleanVisitor<int[],Object> {

    /**
     * Creates a new instance of SATSolver using the provided factory and uses it to
     * translate the given circuit into conjunctive normal form using the
     * <i>definitional translation algorithm</i>. The {@code maxPrimaryVar}
     * parameter is required to contain the maximum label of any primary variable
     * allocated during translation from FOL to boolean. This method assumes that
     * all variables allocated during translation have contiguous labels.
     *
     * @requires let boolFactory = components.circuit | boolFactory.maxVariable() =
     *           maxPrimaryVar && no f: boolFactory.components - BooleanVariable | 1
     *           <= f.label <= maxPrimaryVar
     * @return some cnf: SATSolver | cnf in factory.instance() && max(cnf.variables)
     *         = max(abs(circuit.label), maxPrimaryVar) && meaning(circuit) =
     *         meaning(cnf.clauses)
     */
    static SATSolver translate(final BooleanFormula circuit, final int maxPrimaryVar, final SATFactory factory) {
        final int maxLiteral = StrictMath.abs(circuit.label());
        final Bool2CNFTranslator translator = new Bool2CNFTranslator(factory.instance()) {

            final PolarityDetector pdetector = (new PolarityDetector(maxPrimaryVar, maxLiteral)).apply(circuit);

            @Override
            boolean positive(int label) {
                return pdetector.positive(label);
            }

            @Override
            boolean negative(int label) {
                return pdetector.negative(label);
            }
        };
        return translator.translate(circuit, maxPrimaryVar).solver;
    }

    /**
     * Creates a new instance of SATSolver using the provided factory and
     * initializes it with the trivial translation of the given boolean value. If
     * {@code value} is true, the translation is a solver with no variables and no
     * clauses. Otherwise, the translation is a solver with no variables and a
     * single empty (conflict) clause.
     *
     * @return some cnf : SATSolver | no cnf.variables && (value.booleanValue() =>
     *         no cnf.clauses else (one cnf.clauses && no cnf.clauses.literals))
     */
    static SATSolver translate(BooleanConstant value, final SATFactory factory) {
        final SATSolver cnf = factory.instance();
        if (!value.booleanValue()) {
            cnf.addClause(new int[0]); // unsat
        } // sat
        return cnf;
    }

    /**
     * Returns a new Bool2CNFTranslator that is initialized with the translation of
     * the given circuit. The {@code maxPrimaryVar} parameter is required to contain
     * the maximum label of any primary variable allocated during translation from
     * FOL to boolean.
     *
     * @requires let boolFactory = components.circuit | boolFactory.maxVariable() =
     *           maxPrimaryVar
     * @requires factory.incremental
     * @return some t: Bool2CNFTranslator | t.roots = circuit && t.factory =
     *         components.circuit && max(t.cnf.variables) = max(abs(circuit.label),
     *         maxPrimaryVar) && meaning(circuit) = meaning(t.cnf.clauses)
     */
    static Bool2CNFTranslator translateIncremental(final BooleanFormula circuit, final int maxPrimaryVar, final SATFactory factory) {
        assert factory.incremental();
        final Bool2CNFTranslator translator = new Bool2CNFTranslator(factory.instance()) {};
        return translator.translate(circuit, maxPrimaryVar);
    }

    /**
     * Returns a new Bool2CNFTranslator that is initialized with the trivial
     * translation of the given boolean value. If {@code value} is true, the
     * translation is a solver with no variables and no clauses. Otherwise, the
     * translation is a solver with no variables and a single empty (conflict)
     * clause.
     *
     * @requires factory.incremental
     * @return some t: Bool2CNFTranslator | t.roots = value && no t.cnf.variables &&
     *         (value.booleanValue() => no t.cnf.clauses else (one t.cnf.clauses &&
     *         no t.cnf.clauses.literals))
     */
    static Bool2CNFTranslator translateIncremental(BooleanConstant value, final SATFactory factory) {
        assert factory.incremental();
        return new Bool2CNFTranslator(translate(value, factory)) {};
    }

    /**
     * Updates the given Bool2CNFTranslator with the translation of the given
     * circuit. The behavior of this method is undefined if it is called after
     * translator.solver has returned UNSAT. The {@code maxPrimaryVar} parameter is
     * required to contain the maximum label of any primary variable allocated
     * during translation from FOL to boolean.
     *
     * @requires circuit in translator.factory.components
     * @requires maxPrimaryVar = translator.factory.maxVariable()
     * @requires translator.solver.solve()
     * @ensures translator.roots' = translator.roots + circuit &&
     *          max(translator.cnf.variables) = max(abs(circuit.label),
     *          abs(translator.roots.label), maxPrimaryVar) &&
     *          translator.cnf.clauses in translator.cnf.clauses' &&
     *          translator.cnf.clauses' = CNF(circuit) + translator.cnf.clauses
     * @return translator
     */
    static Bool2CNFTranslator translateIncremental(final BooleanFormula circuit, final int maxPrimaryVar, final Bool2CNFTranslator translator) {
        return translator.translate(circuit, maxPrimaryVar);
    }

    private final SATSolver solver;
    private final IntSet    visited;
    private final int[]     unaryClause   = new int[1];
    private final int[]     binaryClause  = new int[2];
    private final int[]     ternaryClause = new int[3];

    /**
     * Constructs a translator for the given circuit.
     *
     * @requires no solver.variables && solver.clauses
     * @ensures this.solver' = solver
     */
    private Bool2CNFTranslator(SATSolver solver) {
        this.solver = solver;
        this.visited = new IntTreeSet();
    }

    /**
     * Applies this translator to the given circuit, adding the translation of the
     * circuit to this.solver, and returns the translator.
     *
     * @requires circuit in this.factory.components
     * @requires maxPrimaryVar = this.factory.maxPrimaryVariable()
     * @ensures this.solver.variables' = this.solver.variables + { i: int |
     *          solver.numberOfVariables() < i <= max(abs(circuit.label),
     *          maxPrimaryVar) }
     * @effects this.solver.clauses' = this.solver.clauses + CNF(circuit)
     * @return this
     */
    private Bool2CNFTranslator translate(BooleanFormula circuit, int maxPrimaryVar) {
        final int newVars = Math.max(Math.abs(circuit.label()), maxPrimaryVar) - solver.numberOfVariables();
        // System.out.println("circuit.label=" + Math.abs(circuit.label()));
        // System.out.println("maxPrimaryVar=" + maxPrimaryVar);
        // System.out.println("solver.vars=" + solver.numberOfVariables());
        if (newVars > 0)
            solver.addVariables(newVars);

        if (circuit.op() == Operator.AND) {
            for (BooleanFormula input : circuit) {
                input.accept(this, null);
            }
            for (BooleanFormula input : circuit) {
                unaryClause[0] = input.label();
                solver.addClause(unaryClause);
            }
        } else {
            solver.addClause(circuit.accept(this, null));
        }
        return this;
    }

    /**
     * Returns this.solver.
     *
     * @return this.solver
     */
    public SATSolver solver() {
        return solver;
    }

    /**
     * Returns true if the gate with the given label occurs (or may occur)
     * positively in this.roots.
     *
     * @requires some f: (MultiGate + ITEGate) & components.(this.roots) | f.label =
     *           label
     * @return true if the gate with the given label occurs (or may occur)
     *         positively in this.roots
     */
    boolean positive(int label) {
        return true;
    }

    /**
     * Returns true if the gate with the given label occurs (or may occur)
     * negatively in this.roots.
     *
     * @requires some f: (MultiGate + ITEGate) & components.(this.roots) | f.label =
     *           label
     * @return true if the gate with the given label occurs (or may occur)
     *         negatively in this.roots.
     */
    boolean negative(int label) {
        return true;
    }

    /** @return 0->lit */
    private final int[] clause(int lit) {
        unaryClause[0] = lit;
        return unaryClause;
    }

    /** @return 0->lit0 + 1->lit1 */
    private final int[] clause(int lit0, int lit1) {
        binaryClause[0] = lit0;
        binaryClause[1] = lit1;
        return binaryClause;
    }

    /** @return 0->lit0 + 1->lit1 + 2->lit2 */
    private final int[] clause(int lit0, int lit1, int lit2) {
        ternaryClause[0] = lit0;
        ternaryClause[1] = lit1;
        ternaryClause[2] = lit2;
        return ternaryClause;
    }

    /**
     * Adds translation clauses to the solver and returns an array containing the
     * gate's literal. The CNF clauses are generated according to the standard SAT
     * to CNF translation: o = AND(i1, i2, ... ik) ---> (i1 | !o) & (i2 | !o) & ...
     * & (ik | !o) & (!i1 | !i2 | ... | !ik | o), o = OR(i1, i2, ... ik) ---> (!i1 |
     * o) & (!i2 | o) & ... & (!ik | o) & (i1 | i2 | ... | ik | !o).
     *
     * @return o: int[] | o.length = 1 && o.[0] = multigate.literal
     * @ensures if the multigate has not yet been visited, its children are visited
     *          and the clauses are added to the solver connecting the multigate's
     *          literal to its input literal, as described above.
     */
    @Override
    public final int[] visit(MultiGate multigate, Object arg) {
        final int oLit = multigate.label();
        if (visited.add(oLit)) {
            final int sgn;
            final boolean p, n;
            if (multigate.op() == AND) {
                sgn = 1;
                p = positive(oLit);
                n = negative(oLit);
            } else { // multigate.op()==OR
                sgn = -1;
                n = positive(oLit);
                p = negative(oLit);
            }
            final int[] lastClause = n ? new int[multigate.size() + 1] : null;
            final int output = oLit * -sgn;
            int i = 0;
            for (BooleanFormula input : multigate) {
                int iLit = input.accept(this, arg)[0];
                if (p) {
                    solver.addClause(clause(iLit * sgn, output));
                }
                if (n) {
                    lastClause[i++] = iLit * -sgn;
                }
            }
            if (n) {
                lastClause[i] = oLit * sgn;
                solver.addClause(lastClause);
            }
        }
        return clause(oLit);
    }

    /**
     * Adds translation clauses to the solver and returns an array containing the
     * gate's literal. The CNF clauses are generated according to the standard SAT
     * to CNF translation: o = ITE(i, t, e) ---> (!i | !t | o) & (!i | t | !o) & (i
     * | !e | o) & (i | e | !o)
     *
     * @return o: int[] | o.length = 1 && o.[0] = itegate.literal
     * @ensures if the itegate has not yet been visited, its children are visited
     *          and the clauses are added to the solver connecting the multigate's
     *          literal to its input literal, as described above.
     */
    @Override
    public final int[] visit(ITEGate itegate, Object arg) {
        final int oLit = itegate.label();
        if (visited.add(oLit)) {
            final int i = itegate.input(0).accept(this, arg)[0];
            final int t = itegate.input(1).accept(this, arg)[0];
            final int e = itegate.input(2).accept(this, arg)[0];
            final boolean p = positive(oLit), n = negative(oLit);
            if (p) {
                solver.addClause(clause(-i, t, -oLit));
                solver.addClause(clause(i, e, -oLit));
                // redundant clause that strengthens unit propagation
                solver.addClause(clause(t, e, -oLit));
            }
            if (n) {
                solver.addClause(clause(-i, -t, oLit));
                solver.addClause(clause(i, -e, oLit));
                // redundant clause that strengthens unit propagation
                solver.addClause(clause(-t, -e, oLit));
            }
        }
        return clause(oLit);
    }

    /**
     * Returns the negation of the result of visiting negation.input, wrapped in an
     * array.
     *
     * @return o: int[] | o.length = 1 && o[0] = - translate(negation.inputs)[0]
     */
    @Override
    public final int[] visit(NotGate negation, Object arg) {
        return clause(-negation.input(0).accept(this, arg)[0]);
    }

    /**
     * Returns the variable's literal wrapped in a an array.
     *
     * @return o: int[] | o.length = 1 && o[0] = variable.literal
     */
    @Override
    public final int[] visit(BooleanVariable variable, Object arg) {
        return clause(variable.label());
    }

    /**
     * Helper visitor that detects polarity of subformulas.
     *
     * @specfield root: BooleanFormula // the root of the DAG for whose components
     *            we are storing pdetector information
     */
    private static final class PolarityDetector implements BooleanVisitor<Object,Integer> {

        final int               offset;
        /**
         * @invariant all i : [0..polarity.length) | pdetector[i] = 0 <=> formula with
         *            label offset + i has not been visited, pdetector[i] = 1 <=>
         *            formula with label offset + i has been visited with positive
         *            pdetector only, pdetector[i] = 2 <=> formula with label offset + i
         *            has been visited with negative pdetector only, pdetector[i] = 3
         *            <=> formula with label offset + i has been visited with both
         *            polarities
         */
        private final int[]     polarity;
        private final Integer[] ints = {
                                        Integer.valueOf(3), Integer.valueOf(1), Integer.valueOf(2)
        };

        /**
         * Creates a new pdetector detector and applies it to the given circuit. This
         * constructor assumes that all primary variables have contiguous labels, which
         * may not be the case during incremental translation.
         *
         * @requires maxLiteral = |root.label()|
         */
        PolarityDetector(int numPrimaryVars, int maxLiteral) {
            this.offset = numPrimaryVars + 1;
            this.polarity = new int[StrictMath.max(0, maxLiteral - numPrimaryVars)];
        }

        /**
         * Applies this detector to the given formula, and returns this.
         *
         * @requires this.root = root
         * @ensures this.visit(root)
         * @return this
         */
        PolarityDetector apply(BooleanFormula root) {
            root.accept(this, ints[1]);
            return this;
        }

        /**
         * Returns true if the formula with the given label occurs positively in
         * this.root.
         *
         * @requires this visitor has been applied to this.root
         * @requires label in (MultiGate + ITEGate).label
         * @return true if the formula with the given label occurs positively in
         *         this.root.
         */
        boolean positive(int label) {
            return (polarity[label - offset] & 1) > 0;
        }

        /**
         * Returns true if the formula with the given label occurs negatively in
         * this.root.
         *
         * @requires this visitor has been applied to this.root
         * @requires label in (MultiGate + ITEGate).label
         * @return true if the formula with the given label occurs negatively in
         *         this.root.
         */
        boolean negative(int label) {
            return (polarity[label - offset] & 2) > 0;
        }

        /**
         * Returns true if the given formula has been visited with the specified
         * pdetector (1 = positive, 2 = negative, 3 = both). Otherwise records the visit
         * and returns false.
         *
         * @requires formula in (MultiGate + ITEGate)
         * @requires pdetector in this.ints
         * @return true if the given formula has been visited with the specified
         *         pdetector. Otherwise records the visit and returns false.
         */
        private boolean visited(BooleanFormula formula, Integer polarity) {
            final int index = formula.label() - offset;
            final int value = this.polarity[index];
            return (this.polarity[index] = value | polarity) == value;
        }

        @Override
        public Object visit(MultiGate multigate, Integer arg) {
            if (!visited(multigate, arg)) {
                for (BooleanFormula input : multigate) {
                    input.accept(this, arg);
                }
            }
            return null;
        }

        @Override
        public Object visit(ITEGate ite, Integer arg) {
            if (!visited(ite, arg)) {
                // the condition occurs both positively and negative in an ITE
                // gate
                ite.input(0).accept(this, ints[0]);
                ite.input(1).accept(this, arg);
                ite.input(2).accept(this, arg);
            }
            return null;
        }

        @Override
        public Object visit(NotGate negation, Integer arg) {
            return negation.input(0).accept(this, ints[3 - arg]);
        }

        @Override
        public Object visit(BooleanVariable variable, Integer arg) {
            return null; // nothing to do
        }

    }

}
