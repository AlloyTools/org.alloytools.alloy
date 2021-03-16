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

import static kodkod.ast.RelationPredicate.Name.ACYCLIC;
import static kodkod.ast.RelationPredicate.Name.TOTAL_ORDERING;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.RelationPredicate;
import kodkod.ast.RelationPredicate.Name;
import kodkod.engine.bool.BooleanAccumulator;
import kodkod.engine.bool.BooleanConstant;
import kodkod.engine.bool.BooleanFactory;
import kodkod.engine.bool.BooleanMatrix;
import kodkod.engine.bool.BooleanValue;
import kodkod.engine.bool.Operator;
import kodkod.engine.config.Options;
import kodkod.engine.config.Reporter;
import kodkod.instance.Bounds;
import kodkod.instance.TupleFactory;
import kodkod.util.ints.IndexedEntry;
import kodkod.util.ints.IntIterator;
import kodkod.util.ints.IntSet;
import kodkod.util.ints.Ints;
import kodkod.util.nodes.AnnotatedNode;

/**
 * Breaks symmetries for a given problem. Symmetries are broken for total
 * orders, acyclic relations, and via a generic lex-leader predicate.
 *
 * @specfield bounds: Bounds // problem bounds
 * @specfield symmetries: set IntSet
 * @specfield broken: set RelationPredicate
 * @author Emina Torlak
 */
public final class SymmetryBreaker {

    private final Bounds                 bounds;
    private final Set<IntSet>            symmetries;
    private final int                    usize;
    private final AnnotatedNode<Formula> formula;

    /**
     * Constructs a new symmetry breaker for the given Bounds, and calls the given
     * reporter's {@linkplain Reporter#detectedSymmetries(Set)} method with the
     * detected symmetries. <b>Note that the constructor does not make a local copy
     * of the given bounds, so the caller must ensure that all modifications of the
     * given bounds are symmetry preserving.</b>
     *
     * @ensures reporter.detectedSymmetries(this.symmteries')
     * @ensures this.bounds' = bounds && this.symmetries' =
     *          SymmetryDetector.partition(bounds) && no this.broken'
     **/
    public SymmetryBreaker(Bounds bounds, AnnotatedNode<Formula> annotated, Reporter reporter) {
        this.bounds = bounds;
        this.formula = annotated;
        this.usize = bounds.universe().size();
        reporter.detectingSymmetries(bounds);
        this.symmetries = SymmetryDetector.partition(bounds, formula != null ? formula.atomRelations() : null, null);
        reporter.detectedSymmetries(symmetries);
        // System.out.println(symmetries);
    }

    public SymmetryBreaker(Bounds bounds, Reporter reporter) {
        this(bounds, null, reporter);
    }

    /**
     * Breaks matrix symmetries on the relations in this.bounds that are constrained
     * by the total ordering and acyclic predicates, drawn from preds.values(), that
     * make up the keyset of the returned map. After this method returns, the
     * following constraint holds. Let m be the map returned by the method, and
     * m.keySet() be the subset of preds.values() used for symmetry breaking. Then,
     * if we let [[b]] denote the set of constraints specified by a Bounds object b,
     * the formulas "p and [[this.bounds]]" and "m.get(p) and [[this.bounds']]" are
     * equisatisfiable for all p in m.keySet().
     * <p>
     * The value of the "aggressive" flag determines how the symmetries are broken.
     * In particular, if the aggressive flag is true, then the symmetries are broken
     * efficiently, at the cost of losing the information needed to determine
     * whether a predicate in m.keySet() belongs to an unsatisfiable core or not. If
     * the aggressive flag is false, then a less efficient algorithm is applied,
     * which preserves the information necessary for unsatisfiable core extraction.
     * </p>
     * <p>
     * The aggressive symmetry breaking algorithm works as follows. Let t1...tn and
     * c1...ck be the total ordering and acyclic predicates in m.keySet(). For each
     * t in {t1...tn}, this.bounds is modified so that the bounds for t.first,
     * t.last, t.ordered and t.relation are the following constants: t.first is the
     * first atom in the upper bound of t.ordered, t.last is the last atom in the
     * upper bound of t.ordered, t.ordered's lower bound is changed to be equal to
     * its upper bound, and t.relation imposes a total ordering on t.ordered that
     * corresponds to the ordering of the atoms in this.bounds.universe. Then, m is
     * updated with a binding from t to the constant formula TRUE. For each c in
     * {c1...ck}, this.bounds is modified so that the upper bound for c.relation is
     * a tupleset whose equivalent matrix has FALSE in the entries on or below the
     * main diagonal. Then, m is updated with a binding from c to the constant
     * formula TRUE.
     * </p>
     * <p>
     * The lossless symmetry breaking algorithm works as follows. Let t1...tn and
     * c1...ck be the total ordering and acyclic predicates in m.keySet(). For each
     * t in {t1...tn}, three fresh relations are added to this.bounds-- t_first,
     * t_last, t_ordered, and t_order--and constrained as follows: t_first is the
     * first atom in the upper bound of t.ordered, t_last is the last atom in the
     * upper bound of t.ordered, t_ordered is the upper bound of t.ordered, and
     * t_order imposes a total ordering on t.ordered that corresponds to the
     * ordering of the atoms in this.bounds.universe. Then, m is updated with a
     * binding from t to the formula "t.first = t_first and t.last = t_last and
     * t.ordered = t_ordered and t.relation = t.order." For each c in {c1...ck}, a
     * fresh relation c_acyclic is added to this.bounds and constrained to be a
     * constant whose equivalent matrix has no entries on or below the main
     * diagonal. The map m is then updated with a binding from c to the constraint
     * "c in c_acyclic".
     * </p>
     *
     * @ensures this.bounds' is modified as described above
     * @ensures this.symmetries' is modified to no longer contain the partitions
     *          that made up the bounds of the relations on which symmetries have
     *          been broken
     * @return a map m such that m.keySet() in preds.values(), and for all
     *         predicates p in m.keySet(), the formulas "p and [[this.bounds]]" and
     *         "m.get(p) and [[this.bounds']]" are equisatisfiable
     */
    public Map<RelationPredicate,Formula> breakMatrixSymmetries(Map<Name,Set<RelationPredicate>> preds, boolean aggressive) {
        final Set<RelationPredicate> totals = preds.get(TOTAL_ORDERING);
        final Set<RelationPredicate> acyclics = preds.get(ACYCLIC);
        final Map<RelationPredicate,Formula> broken = new IdentityHashMap<RelationPredicate,Formula>();

        for (RelationPredicate.TotalOrdering pred : sort(totals.toArray(new RelationPredicate.TotalOrdering[totals.size()]))) {
            Formula replacement = breakTotalOrder(pred, aggressive);
            if (replacement != null)
                broken.put(pred, replacement);
        }

        for (RelationPredicate.Acyclic pred : sort(acyclics.toArray(new RelationPredicate.Acyclic[acyclics.size()]))) {
            Formula replacement = breakAcyclic(pred, aggressive);
            if (replacement != null)
                broken.put(pred, replacement);
        }

        return broken;
    }

    /**
     * Generates a lex leader symmetry breaking predicate for this.symmetries (if
     * any), using the specified leaf interpreter and options.symmetryBreaking. It
     * also invokes options.reporter().generatingSBP() if a non-constant predicate
     * is generated.
     *
     * @requires interpreter.relations in this.bounds.relations
     * @ensures options.reporter().generatingSBP() if a non-constant predicate is
     *          generated.
     * @return a symmetry breaking predicate for this.symmetries
     */
    public final BooleanValue generateSBP(LeafInterpreter interpreter, Options options) {
        final int predLength = options.symmetryBreaking();
        if (symmetries.isEmpty() || predLength == 0)
            return BooleanConstant.TRUE;
        options.reporter().generatingSBP();

        final List<RelationParts> relParts = relParts();
        final BooleanFactory factory = interpreter.factory();
        final BooleanAccumulator sbp = BooleanAccumulator.treeGate(Operator.AND);
        final List<BooleanValue> original = new ArrayList<BooleanValue>(predLength);
        final List<BooleanValue> permuted = new ArrayList<BooleanValue>(predLength);

        for (IntSet sym : symmetries) {

            IntIterator indeces = sym.iterator();
            for (int prevIndex = indeces.next(); indeces.hasNext();) {
                int curIndex = indeces.next();
                for (Iterator<RelationParts> rIter = relParts.iterator(); rIter.hasNext() && original.size() < predLength;) {

                    RelationParts rparts = rIter.next();
                    Relation r = rparts.relation;

                    if (!rparts.representatives.contains(sym.min()))
                        continue; // r does not range over sym

                    BooleanMatrix m = interpreter.interpret(r);
                    for (IndexedEntry<BooleanValue> entry : m) {
                        int permIndex = permutation(r.arity(), entry.index(), prevIndex, curIndex);
                        BooleanValue permValue = m.get(permIndex);
                        if (permIndex == entry.index() || atSameIndex(original, permValue, permuted, entry.value()))
                            continue;

                        original.add(entry.value());
                        permuted.add(permValue);
                    }
                }

                sbp.add(leq(factory, original, permuted));
                original.clear();
                permuted.clear();
                prevIndex = curIndex;
            }
        }
        symmetries.clear(); // no symmetries left to break (this is
                           // conservative)
        return factory.accumulate(sbp);
    }

    /**
     * Returns a list of RelationParts that map each non-constant r in
     * this.bounds.relations to the representatives of the sets from this.symmetries
     * contained in the upper bound of r. The entries are sorted by relations'
     * arities and names.
     *
     * @return a list of RelationParts that contains an entry for each non-constant
     *         r in this.bounds.relations and the representatives of sets from
     *         this.symmetries contained in the upper bound of r.
     */
    private List<RelationParts> relParts() {
        final List<RelationParts> relParts = new ArrayList<RelationParts>(bounds.relations().size());
        for (Relation r : bounds.relations()) {
            IntSet upper = bounds.upperBound(r).indexView();
            if (upper.size() == bounds.lowerBound(r).size())
                continue; // skip constant relation
            IntSet reps = Ints.bestSet(usize);
            for (IntIterator tuples = upper.iterator(); tuples.hasNext();) {
                for (int tIndex = tuples.next(), i = r.arity(); i > 0; i--, tIndex /= usize) {
                    for (IntSet symm : symmetries) {
                        if (symm.contains(tIndex % usize)) {
                            reps.add(symm.min());
                            break;
                        }
                    }
                }
            }
            relParts.add(new RelationParts(r, reps));
        }
        final Comparator<RelationParts> cmp = new Comparator<RelationParts>() {

            @Override
            public int compare(RelationParts o1, RelationParts o2) {
                final int acmp = o1.relation.arity() - o2.relation.arity();
                return acmp != 0 ? acmp : String.valueOf(o1.relation.name()).compareTo(String.valueOf(o2.relation.name()));
            }
        };
        Collections.sort(relParts, cmp);
        return relParts;
    }

    /**
     * Returns a BooleanValue that is true iff the string of bits represented by l0
     * is lexicographically less than or equal to the string of bits reprented by
     * l1.
     *
     * @requires l0.size()==l1.size()
     * @return a circuit that compares l0 and l1
     */
    private static final BooleanValue leq(BooleanFactory f, List<BooleanValue> l0, List<BooleanValue> l1) {
        final BooleanAccumulator cmp = BooleanAccumulator.treeGate(Operator.AND);
        BooleanValue prevEquals = BooleanConstant.TRUE;
        for (int i = 0; i < l0.size(); i++) {
            cmp.add(f.implies(prevEquals, f.implies(l0.get(i), l1.get(i))));
            prevEquals = f.and(prevEquals, f.iff(l0.get(i), l1.get(i)));
        }
        return f.accumulate(cmp);
    }

    /**
     * Let t be the tuple represent by the given arity and tupleIndex. This method
     * returns the tuple index of the tuple t' such t' is equal to t with each
     * occurence of atomIndex0 replaced by atomIndex1 and vice versa.
     *
     * @return the index of the tuple to which the given symmetry maps the tuple
     *         specified by arith and tupleIndex
     */
    private final int permutation(int arity, int tupleIndex, int atomIndex0, int atomIndex1) {
        int permIndex = 0;
        for (int u = 1; arity > 0; arity--, tupleIndex /= usize, u *= usize) {
            int atomIndex = tupleIndex % usize;
            if (atomIndex == atomIndex0)
                permIndex += atomIndex1 * u;
            else if (atomIndex == atomIndex1) {
                permIndex += atomIndex0 * u;
            } else {
                permIndex += atomIndex * u;
            }
        }
        return permIndex;
    }

    /**
     * Returns true if there is some index i such that l0[i] = v0 and l1[i] = v1.
     *
     * @requires l0.size()=l1.size()
     * @return some i: int | l0[i] = v0 && l1[i] = v1
     */
    private static boolean atSameIndex(List<BooleanValue> l0, BooleanValue v0, List<BooleanValue> l1, BooleanValue v1) {
        for (int i = 0; i < l0.size(); i++) {
            if (l0.get(i).equals(v0) && l1.get(i).equals(v1))
                return true;
        }
        return false;
    }

    /**
     * Sorts the predicates in the given array in the ascending order of the names
     * of the predicates' relations, and returns it.
     *
     * @return broken'
     * @ensures all i: [0..preds.size()) | all j: [0..i) | broken[j].relation.name
     *          <= broken[i].relation.name
     */
    private static final <P extends RelationPredicate> P[] sort(final P[] preds) {
        final Comparator<RelationPredicate> cmp = new Comparator<RelationPredicate>() {

            @Override
            public int compare(RelationPredicate o1, RelationPredicate o2) {
                return String.valueOf(o1.relation().name()).compareTo(String.valueOf(o2.relation().name()));
            }
        };
        Arrays.sort(preds, cmp);
        return preds;
    }

    /**
     * If possible, breaks symmetry on the given acyclic predicate and returns a
     * formula f such that the meaning of acyclic with respect to this.bounds is
     * equivalent to the meaning of f with respect to this.bounds'. If symmetry
     * cannot be broken on the given predicate, returns null.
     * <p>
     * We break symmetry on the relation constrained by the given predicate iff
     * this.bounds.upperBound[acyclic.relation] is the cross product of some
     * partition in this.symmetries with itself. Assuming that this is the case, we
     * then break symmetry on acyclic.relation using one of the methods described in
     * {@linkplain #breakMatrixSymmetries(Map, boolean)}; the method used depends on
     * the value of the "agressive" flag. The partition that formed the upper bound
     * of acylic.relation is removed from this.symmetries.
     * </p>
     *
     * @return null if symmetry cannot be broken on acyclic; otherwise returns a
     *         formula f such that the meaning of acyclic with respect to
     *         this.bounds is equivalent to the meaning of f with respect to
     *         this.bounds'
     * @ensures this.symmetries and this.bounds are modified as described in
     *          {@linkplain #breakMatrixSymmetries(Map, boolean)} iff
     *          this.bounds.upperBound[acyclic.relation] is the cross product of
     *          some partition in this.symmetries with itself
     * @see #breakMatrixSymmetries(Map,boolean)
     */
    private final Formula breakAcyclic(RelationPredicate.Acyclic acyclic, boolean aggressive) {
        final IntSet[] colParts = symmetricColumnPartitions(acyclic.relation());
        if (colParts != null) {
            final Relation relation = acyclic.relation();
            final IntSet upper = bounds.upperBound(relation).indexView();
            final IntSet reduced = Ints.bestSet(usize * usize);
            for (IntIterator tuples = upper.iterator(); tuples.hasNext();) {
                int tuple = tuples.next();
                int mirror = (tuple / usize) + (tuple % usize) * usize;
                if (tuple != mirror) {
                    if (!upper.contains(mirror))
                        return null;
                    if (!reduced.contains(mirror))
                        reduced.add(tuple);
                }
            }

            // remove the partition from the set of symmetric partitions
            removePartition(colParts[0].min());

            if (aggressive) {
                bounds.bound(relation, bounds.universe().factory().setOf(2, reduced));
                return Formula.TRUE;
            } else {
                final Relation acyclicConst = Relation.binary("SYM_BREAK_CONST_" + acyclic.relation().name());
                bounds.boundExactly(acyclicConst, bounds.universe().factory().setOf(2, reduced));
                return relation.in(acyclicConst);
            }
        }
        return null;
    }

    /**
     * If possible, breaks symmetry on the given total ordering predicate and
     * returns a formula f such that the meaning of total with respect to
     * this.bounds is equivalent to the meaning of f with respect to this.bounds'.
     * If symmetry cannot be broken on the given predicate, returns null.
     * <p>
     * We break symmetry on the relation constrained by the given predicate iff
     * total.first, total.last, and total.ordered have the same upper bound, which,
     * when cross-multiplied with itself gives the upper bound of total.relation.
     * Assuming that this is the case, we then break symmetry on total.relation,
     * total.first, total.last, and total.ordered using one of the methods described
     * in {@linkplain #breakMatrixSymmetries(Map, boolean)}; the method used depends
     * on the value of the "agressive" flag. The partition that formed the upper
     * bound of total.ordered is removed from this.symmetries.
     * </p>
     *
     * @return null if symmetry cannot be broken on total; otherwise returns a
     *         formula f such that the meaning of total with respect to this.bounds
     *         is equivalent to the meaning of f with respect to this.bounds'
     * @ensures this.symmetries and this.bounds are modified as desribed in
     *          {@linkplain #breakMatrixSymmetries(Map, boolean)} iff total.first,
     *          total.last, and total.ordered have the same upper bound, which, when
     *          cross-multiplied with itself gives the upper bound of total.relation
     * @see #breakMatrixSymmetries(Map,boolean)
     */
    private final Formula breakTotalOrder(RelationPredicate.TotalOrdering total, boolean aggressive) {
        final Relation first = total.first(), last = total.last(), ordered = total.ordered(),
                        relation = total.relation();
        final IntSet domain = bounds.upperBound(ordered).indexView();

        if (symmetricColumnPartitions(ordered) != null && bounds.upperBound(first).indexView().contains(domain.min()) && bounds.upperBound(last).indexView().contains(domain.max())) {

            // construct the natural ordering that corresponds to the ordering
            // of the atoms in the universe
            final IntSet ordering = Ints.bestSet(usize * usize);
            int prev = domain.min();
            for (IntIterator atoms = domain.iterator(prev + 1, usize); atoms.hasNext();) {
                int next = atoms.next();
                ordering.add(prev * usize + next);
                prev = next;
            }

            if (ordering.containsAll(bounds.lowerBound(relation).indexView()) && bounds.upperBound(relation).indexView().containsAll(ordering)) {

                // remove the ordered partition from the set of symmetric
                // partitions
                removePartition(domain.min());

                final TupleFactory f = bounds.universe().factory();

                if (aggressive) {
                    bounds.boundExactly(first, f.setOf(f.tuple(1, domain.min())));
                    bounds.boundExactly(last, f.setOf(f.tuple(1, domain.max())));
                    bounds.boundExactly(ordered, bounds.upperBound(total.ordered()));
                    bounds.boundExactly(relation, f.setOf(2, ordering));

                    return Formula.TRUE;

                } else {
                    final Relation firstConst = Relation.unary("SYM_BREAK_CONST_" + first.name());
                    final Relation lastConst = Relation.unary("SYM_BREAK_CONST_" + last.name());
                    final Relation ordConst = Relation.unary("SYM_BREAK_CONST_" + ordered.name());
                    final Relation relConst = Relation.binary("SYM_BREAK_CONST_" + relation.name());
                    bounds.boundExactly(firstConst, f.setOf(f.tuple(1, domain.min())));
                    bounds.boundExactly(lastConst, f.setOf(f.tuple(1, domain.max())));
                    bounds.boundExactly(ordConst, bounds.upperBound(total.ordered()));
                    bounds.boundExactly(relConst, f.setOf(2, ordering));

                    return Formula.and(first.eq(firstConst), last.eq(lastConst), ordered.eq(ordConst), relation.eq(relConst));
                    // return first.eq(firstConst).and(last.eq(lastConst)).and(
                    // ordered.eq(ordConst)).and( relation.eq(relConst));
                }

            }
        }

        return null;
    }

    /**
     * Removes from this.symmetries the partition that contains the specified atom.
     *
     * @ensures this.symmetries' = { s: this.symmetries | !s.contains(atom) }
     */
    private final void removePartition(int atom) {
        for (Iterator<IntSet> symIter = symmetries.iterator(); symIter.hasNext();) {
            if (symIter.next().contains(atom)) {
                symIter.remove();
                break;
            }
        }
    }

    /**
     * If all columns of the upper bound of r are symmetric partitions, those
     * partitions are returned. Otherwise null is returned.
     *
     * @return (all i: [0..r.arity) | some s: symmetries[int] |
     *         bounds.upperBound[r].project(i).indexView() = s) => {colParts:
     *         [0..r.arity)->IntSet | all i: [0..r.arity()) | colParts[i] =
     *         bounds.upperBound[r].project(i).indexView() }, null
     */
    private final IntSet[] symmetricColumnPartitions(Relation r) {
        final IntSet upper = bounds.upperBound(r).indexView();
        if (upper.isEmpty())
            return null;

        final IntSet[] colParts = new IntSet[r.arity()];
        for (int i = r.arity() - 1, min = upper.min(); i >= 0; i--, min /= usize) {
            for (IntSet part : symmetries) {
                if (part.contains(min % usize)) {
                    colParts[i] = part;
                    break;
                }
            }
            if (colParts[i] == null)
                return null;
        }
        for (IntIterator tuples = upper.iterator(); tuples.hasNext();) {
            for (int i = r.arity() - 1, tuple = tuples.next(); i >= 0; i--, tuple /= usize) {
                if (!colParts[i].contains(tuple % usize))
                    return null;
            }
        }
        return colParts;
    }

    /**
     * An entry for a relation and the representative (least atom) for each symmetry
     * class in the relation's upper bound.
     */
    private static final class RelationParts {

        final Relation relation;
        final IntSet   representatives;

        RelationParts(Relation relation, IntSet representatives) {
            this.relation = relation;
            this.representatives = representatives;
        }
    }
}
