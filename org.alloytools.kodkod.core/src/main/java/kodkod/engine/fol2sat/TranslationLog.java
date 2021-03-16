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

import java.util.Iterator;
import java.util.Set;

import kodkod.ast.Formula;
import kodkod.engine.config.Options;
import kodkod.instance.Bounds;

/**
 * A log of the translations of the descendants of a given formula that are
 * either formulas or that desugar to formulas.
 *
 * @specfield originalFormula: Formula // the original formula, as constructed
 *            by client
 * @specfield originalBounds: Bounds // the original bounds, as constructed by
 *            client
 * @specfield formula: Formula // optimization of this.originalFormula that was
 *            used for translation
 * @specfield bounds: Bounds // optimization of this.originalBounds that was
 *            used for translation
 * @specfield records: set TranslationRecord
 * @specfield replay: [0..#records) one->one records // replay order -- i.e. the
 *            order in the which records were added to the log
 * @invariant all r: records | r.node in formula.*children
 * @invariant Solver.solve(formula, bounds).instance() == null iff
 *            Solver.solve(originalFormula, originalBounds).instance() == null
 * @author Emina Torlak
 */
public abstract class TranslationLog {

    TranslationLog() {}

    /**
     * Returns the roots of this.formula. In other words, returns the subformulas,
     * {f0, ..., fk}, of this.formula such that, for all 0<=i<=k, f<sub>i</sub> [[f0
     * && ... && fk]] <=> [[formula]]. The granularity of the subdivision of
     * this.formula into roots depends on the core granularity specified in the
     * {@linkplain Options} that were used when translating this.formula.
     * <p>
     * Unless a given root translates to a constant, the highest magnitude literal
     * corresponding to each root (as given by this.records) is guaranteed to be
     * present in the translation of this.formula as a unit clause. All the
     * remaining clauses (except those comprising the symmetry breaking predicate,
     * encoded with its own unit clause containing the maximum literal) that are
     * reachable from such a unit clause represent the translations of the given
     * root's descendants. We define reachability over the clauses in a translation
     * as follows: let l1 be the highest magnitude literal in the clause c1, and let
     * l2 be the highest magnitude literal in c2. If l2 occurs in c1 (in any
     * polarity), then there is an edge from c1 and c2. The unit clauses are always
     * the last clauses to be added to a SAT solver during translation.
     * </p>
     *
     * @return roots of this.formula
     */
    public abstract Set<Formula> roots();

    /**
     * Returns this.bounds.
     *
     * @return this.bounds.
     */
    public abstract Bounds bounds();

    /**
     * Returns an iterator over the translation records in this log that are
     * accepted by the given filter. The iterator returns the records in the order
     * in which they were generated. This guarantees that records for the
     * descendants of a node are always returned before the record for the node
     * itself.
     * <p>
     * <b>Note:</b>The record objects returned by the iterator are not required to
     * be immutable. In particular, the state of a record object returned by
     * <tt>next()</tt> is guaranteed to remain the same only until the subsequent
     * call to <tt>next()</tt>.
     * </p>
     *
     * @return an iterator, in the proper replay sequence, over the translation
     *         records in this log that are accepted by the given filter.
     */
    public abstract Iterator<TranslationRecord> replay(RecordFilter filter);

    /**
     * Returns an iterator over all translation records in this log. The iterator
     * returns the records in the order in which they were generated. This
     * guarantees that records for the descendants of a node are always returned
     * before the record for the node itself. The effect of this method is the same
     * as calling {@linkplain #replay(RecordFilter) replay(RecordFilter.ALL)}.
     * <p>
     * <b>Note:</b>The record objects returned by the iterator are not required to
     * be immutable. In particular, the state of a record object returned by
     * <tt>next()</tt> is guaranteed to remain the same only until the subsequent
     * call to <tt>next()</tt>.
     * </p>
     *
     * @return an iterator over all translation records in this.log, in the proper
     *         replay sequence.
     * @see #replay(RecordFilter)
     */
    public final Iterator<TranslationRecord> replay() {
        return replay(RecordFilter.ALL);
    }

    // /**
    // * Compresses this translation log (optional operation) by eliminating
    // * redundant records.
    // * @ensures all r: this.records | one r': this.records' | r.node = r'.node
    // && r.literal = r'.literal && r.env.equals(r'.env)
    // * @throws UnsupportedOperationException this log does not support
    // compression
    // */
    // public abstract void compress();
}
