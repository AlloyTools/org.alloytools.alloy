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

import java.util.Collections;
import java.util.Iterator;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Node;
import kodkod.ast.Variable;
import kodkod.engine.Solver;
import kodkod.engine.bool.BooleanMatrix;
import kodkod.engine.bool.BooleanValue;
import kodkod.instance.Bounds;
import kodkod.instance.TupleSet;
import kodkod.util.collections.FixedMap;
import kodkod.util.nodes.AnnotatedNode;
import kodkod.util.nodes.Nodes;

/**
 * A translation logger that logs translation events for the
 * {@linkplain Nodes#conjuncts(Formula) conjuncts} of a given formula to memory.
 * In other words, this logger only logs the translations for the children of
 * the given formula, if the formula is a conjunction. Otherwise, it simply logs
 * the translation for the formula itself. The translation events for the
 * conjuncts' descendants are ignored.
 *
 * @specfield originalFormula: Formula // the
 *            {@linkplain Solver#solve(Formula, kodkod.instance.Bounds)
 *            original} formula, provided by the user
 * @specfield originalBounds: Bounds // the
 *            {@linkplain Solver#solve(Formula, kodkod.instance.Bounds)
 *            original} bounds, provided by the user
 * @specfield formula: Formula // desugaring of this.formula that was translated
 * @specfield bounds: Bounds // translation bounds
 * @specfield records: (formula.*children & Formula) -> BooleanValue ->
 *            Environment<BooleanMatrix>
 * @invariant Solver.solve(formula, bounds).instance() == null iff
 *            Solver.solve(originalFormula, originalBounds).instance() == null
 * @author Emina Torlak
 */
final class MemoryLogger extends TranslationLogger {

    private final FixedMap<Formula,BooleanValue> logMap;
    private final AnnotatedNode<Formula>         annotated;
    private final Bounds                         bounds;

    /**
     * Constructs a new memory logger from the given annotated formula.
     *
     * @ensures this.formula' = annotated.node
     * @ensures this.bounds' = bounds
     * @ensures no this.records'
     * @ensures this.log().roots() = Nodes.conjuncts(annotated)
     */
    MemoryLogger(final AnnotatedNode<Formula> annotated, Bounds bounds) {
        this.annotated = annotated;
        this.bounds = bounds;
        this.logMap = new FixedMap<Formula,BooleanValue>(Nodes.conjuncts(annotated.node()));
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.fol2sat.TranslationLogger#close()
     */
    @Override
    void close() {}

    /**
     * Logs the translation of the given formula if and only if f is a root of
     * this.formula.
     *
     * @ensures f in Nodes.conjuncts(this.formula) and no this.records[f] =>
     *          this.records' = this.records ++ f -> translation -> env
     * @throws IllegalArgumentException some this.records[f] and this.records[f] !=
     *             translation -> env
     * @see kodkod.engine.fol2sat.TranslationLogger#log(kodkod.ast.Formula,
     *      kodkod.engine.bool.BooleanValue, kodkod.engine.fol2sat.Environment)
     */
    @Override
    void log(Formula f, BooleanValue translation, Environment<BooleanMatrix,Expression> env) {
        if (logMap.containsKey(f)) {
            // assert env.isEmpty();
            final BooleanValue old = logMap.put(f, translation);
            if (old != null && old != translation)
                throw new IllegalArgumentException("translation of root corresponding to the formula has already been logged: " + f);
        }
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.fol2sat.TranslationLogger#log()
     */
    @Override
    TranslationLog log() {
        return new MemoryLog(annotated, logMap, bounds);
    }

    /**
     * A memory-based translation log, written by a MemoryLogger.
     *
     * @author Emina Torlak
     */
    private static class MemoryLog extends TranslationLog {

        private final Set<Formula> roots;
        private final Bounds       bounds;
        private final Node[]       original;
        private final int[]        transl;

        /**
         * Constructs a new memory log out of the given node and its corresponding log
         * map.
         */
        MemoryLog(AnnotatedNode<Formula> annotated, FixedMap<Formula,BooleanValue> logMap, Bounds bounds) {
            this.bounds = bounds;
            this.roots = Nodes.conjuncts(annotated.node());
            assert roots.size() == logMap.size();
            this.transl = new int[roots.size()];
            this.original = new Node[roots.size()];
            final Iterator<Formula> itr = roots.iterator();
            for (int i = 0; i < transl.length; i++) {
                final Formula root = itr.next();
                transl[i] = logMap.get(root).label();
                original[i] = annotated.sourceOf(root);
            }
        }

        /**
         * {@inheritDoc}
         *
         * @see kodkod.engine.fol2sat.TranslationLog#bounds()
         */
        @Override
        public Bounds bounds() {
            return bounds;
        }

        /**
         * {@inheritDoc}
         *
         * @see kodkod.engine.fol2sat.TranslationLog#replay(kodkod.engine.fol2sat.RecordFilter)
         */
        @Override
        public Iterator<TranslationRecord> replay(final RecordFilter filter) {
            return new Iterator<TranslationRecord>() {

                final Iterator<Formula> itr     = roots.iterator();
                boolean                 ready   = false;
                int                     index   = -1;
                Formula                 root    = null;
                final TranslationRecord current = new TranslationRecord() {

                                                    @Override
                                                    public Map<Variable,TupleSet> env() {
                                                        return Collections.emptyMap();
                                                    }

                                                    @Override
                                                    public int literal() {
                                                        return transl[index];
                                                    }

                                                    @Override
                                                    public Node node() {
                                                        return original[index];
                                                    }

                                                    @Override
                                                    public Formula translated() {
                                                        return root;
                                                    }

                                                };

                @Override
                @SuppressWarnings("unchecked" )
                public boolean hasNext() {
                    while (!ready && itr.hasNext()) {
                        root = itr.next();
                        index++;
                        if (filter.accept(original[index], root, transl[index], Collections.EMPTY_MAP)) {
                            ready = true;
                            break;
                        }
                    }
                    return ready;
                }

                @Override
                public TranslationRecord next() {
                    if (!hasNext())
                        throw new NoSuchElementException();
                    ready = false;
                    return current;
                }

                @Override
                public void remove() {
                    throw new UnsupportedOperationException();
                }
            };
        }

        /**
         * {@inheritDoc}
         *
         * @see kodkod.engine.fol2sat.TranslationLog#roots()
         */
        @Override
        public Set<Formula> roots() {
            return roots;
        }

    }

}
