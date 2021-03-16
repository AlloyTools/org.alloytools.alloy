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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Set;

import kodkod.ast.Relation;
import kodkod.instance.Bounds;
import kodkod.instance.TupleSet;
import kodkod.util.ints.IntIterator;
import kodkod.util.ints.IntSet;
import kodkod.util.ints.Ints;

/**
 * Partitions a universe into equivalence classes based on the bounding
 * constraints given by a Bounds object. In particular, given a {@link Bounds}
 * object {@code b}, a {@link SymmetryDetector} computes the coarsest partition
 * <code>{ s0, ..., sn }</code> of <code>b.universe</code> such that every
 * tupleset in <code>b.lowerBound</code>, <code>b.upperBound</code>, and
 * <code>b.intBound</code> can be expressed as a union of cross-products of sets
 * drawn from <code>{ s0, ..., sn }</code>.
 *
 * @author Emina Torlak
 */
public final class SymmetryDetector {

    private final Bounds               bounds;
    /*
     * invariant: representatives always holds a sequence of IntSets that partition
     * bounds.universe
     */
    private final List<IntSet>         parts;
    private final int                  usize;
    private final Collection<Relation> ignoreAllAtomRelsExcept;
    private final Collection<Relation> ignoreRels;

    /**
     * Constructs a new SymmetryDetector for the given bounds.
     *
     * @ensures this.bounds' = bounds
     */
    private SymmetryDetector(Bounds bounds, Collection<Relation> ignoreAllAtomRelsExcept, Collection<Relation> ignoreRels) {
        this.bounds = bounds;
        this.usize = bounds.universe().size();
        this.ignoreAllAtomRelsExcept = ignoreAllAtomRelsExcept;
        this.ignoreRels = ignoreRels;

        // start with the maximum partition -- the whole universe.
        this.parts = new LinkedList<IntSet>();
        final IntSet set = Ints.bestSet(usize);
        for (int i = 0; i < usize; i++) {
            set.add(i);
        }
        this.parts.add(set);
    }

    /**
     * Returns the coarsest sound partition of {@code bounds.universe} into symmetry
     * classes.
     *
     * @return some symmetries: set IntSet | (symmetries.ints = { i: int | 0 <= i <
     *         bounds.universe.size() }) && (all p1, p2: symmetries | some p1.ints &
     *         p2.ints => p1 = p2) && (all ts: bounds.(lowerBound + upperBound +
     *         intBound)[Relation] | some decomposition: set List<IntSet> |
     *         decomposition.elements[int] in symmetries &&
     *         decomposition.elements.IntSet = { i: int | 0 <= i < ts.arity } &&
     *         ts.tuples = { t: Tuple | some part: decomposition | all i: [0 ..
     *         ts.arity-1] | t.atomIndex(i) in part.get(i) }) && (all other: set
     *         IntSet | #other > #symmetries => some ts: bounds.(lowerBound +
     *         upperBound + intBound)[Relation] | no decomposition: set List<IntSet>
     *         | decomposition.elements[int] in other &&
     *         decomposition.elements.IntSet = { i: int | 0 <= i < ts.arity } &&
     *         ts.tuples = { t: Tuple | some part: decomposition | all i: [0 ..
     *         ts.arity-1] | t.atomIndex(i) in part.get(i) })
     */
    public static Set<IntSet> partition(Bounds bounds) {
        // TODO: remove and decide at every call site
        return partition(bounds, null, null); // new ArrayList<Relation>(),
                                             // null);
    }

    public static Set<IntSet> partition(Bounds bounds, Collection<Relation> ignoreAllAtomRelsExcept, Collection<Relation> ignoreRelations) {
        final SymmetryDetector detector = new SymmetryDetector(bounds, ignoreAllAtomRelsExcept, ignoreRelations);
        detector.computePartitions();
        final Set<IntSet> parts = new LinkedHashSet<IntSet>(detector.parts);
        assert parts.size() == detector.parts.size(); // sanity check
        return parts;
    }

    /**
     * Partitions this.bounds.universe into sets of equivalent atoms.
     *
     * @ensures all disj s, q: this.parts'[int] | some s.ints && some q.ints && (no
     *          s.ints & q.ints) && this.parts'[int].ints =
     *          [0..this.bounds.universe.size()) && (all ts:
     *          this.bounds.lowerBound[Relation] + this.bounds.upperBound[Relation]
     *          | all s: this.parts'[int] | all a1, a2:
     *          this.bounds.universe.atoms[s.ints] | all t1, t2: ts.tuples |
     *          t1.atoms[0] = a1 && t2.atoms[0] = a2 => t1.atoms[1..ts.arity) =
     *          t1.atoms[1..ts.arity) || t1.atoms[1..ts.arity) = a1 &&
     *          t1.atoms[1..ts.arity) = a2)
     */
    private final void computePartitions() {
        if (usize == 1)
            return; // nothing more to do

        final Map<IntSet,IntSet> range2domain = new HashMap<IntSet,IntSet>((usize * 2) / 3);

        // refine the partitions based on the bounds for each integer
        for (IntIterator iter = bounds.ints().iterator(); iter.hasNext();) {
            TupleSet exact = bounds.exactBound(iter.next());
            refinePartitions(exact.indexView(), 1, range2domain);
        }

        // refine the partitions based on the upper/lower bounds for each
        // relation
        for (TupleSet s : sort(bounds)) {
            if (parts.size() == usize)
                return;
            refinePartitions(s.indexView(), s.arity(), range2domain);
        }

    }

    /**
     * Returns an array that contains unique non-empty tuplesets in the given
     * bounds, sorted in the order of increasing size.
     *
     * @return unique non-empty tuplesets in the given bounds, sorted in the order
     *         of increasing size.
     */
    private TupleSet[] sort(Bounds bounds) {
        final List<TupleSet> sets = new ArrayList<TupleSet>(bounds.relations().size());
        for (Relation r : bounds.relations()) {
            if (r.isAtom() && ignoreAllAtomRelsExcept != null && !ignoreAllAtomRelsExcept.contains(r))
                continue;
            if (ignoreRels != null && ignoreRels.contains(r))
                continue;
            final TupleSet lower = bounds.lowerBound(r);
            final TupleSet upper = bounds.upperBound(r);
            if (!lower.isEmpty() && lower.size() < upper.size()) {
                sets.add(lower);
            }
            if (!upper.isEmpty()) {
                sets.add(upper);
            }
        }
        final TupleSet[] sorted = sets.toArray(new TupleSet[sets.size()]);
        Arrays.sort(sorted, new Comparator<TupleSet>() {

            @Override
            public int compare(TupleSet o1, TupleSet o2) {
                return o1.size() - o2.size();
            }
        });
        return sorted;
    }

    /**
     * Refines the atomic partitions in this.parts based on the contents of the
     * given tupleset, decomposed into its constituent IntSet and arity. The
     * range2domain map is used for intermediate computations for efficiency (to
     * avoid allocating it in each recursive call).
     *
     * @requires all disj s, q: this.parts[int] | some s.ints && some q.ints && (no
     *           s.ints & q.ints) && this.parts[int].ints =
     *           [0..this.bounds.universe.size())
     * @ensures let usize = this.bounds.universe.size(), firstColFactor =
     *          usize^(arit-1) | all disj s, q: this.parts'[int] | some s.ints &&
     *          some q.ints && (no s.ints & q.ints) && this.parts'[int].ints =
     *          [0..usize) && all s: this.parts'[int] | all a1, a2:
     *          this.bounds.universe.atoms[s.ints] | all t1, t2: set.ints | t1 /
     *          firstColFactor = a1 && t2 / firstColFactor = a2 => t1 %
     *          firstColFactor = t2 % firstColFactor || t1 = a1*((1 -
     *          firstColFactor) / (1 - usize)) && t2 = a2*((1 - firstColFactor) / (1
     *          - usize)))
     */
    private void refinePartitions(IntSet set, int arity, Map<IntSet,IntSet> range2domain) {
        if (arity == 1) {
            refinePartitions(set);
            return;
        }

        final List<IntSet> otherColumns = new LinkedList<IntSet>();
        int firstColFactor = (int) StrictMath.pow(usize, arity - 1);
        IntSet firstCol = Ints.bestSet(usize);
        for (IntIterator rbIter = set.iterator(); rbIter.hasNext();) {
            firstCol.add(rbIter.next() / firstColFactor);
        }
        refinePartitions(firstCol);

        int idenFactor = (1 - firstColFactor) / (1 - usize);
        for (ListIterator<IntSet> partsIter = parts.listIterator(); partsIter.hasNext();) {
            IntSet part = partsIter.next();
            if (firstCol.contains(part.min())) { // contains one, contains them
                                                // all
                range2domain.clear();
                for (IntIterator atoms = part.iterator(); atoms.hasNext();) {
                    int atom = atoms.next();
                    IntSet atomRange = Ints.bestSet(firstColFactor);
                    for (IntIterator rbIter = set.iterator(atom * firstColFactor, (atom + 1) * firstColFactor - 1); rbIter.hasNext();) {
                        atomRange.add(rbIter.next() % firstColFactor);
                    }
                    IntSet atomDomain = range2domain.get(atomRange);
                    if (atomDomain != null)
                        atomDomain.add(atom);
                    else
                        range2domain.put(atomRange, oneOf(usize, atom));
                }
                partsIter.remove();
                IntSet idenPartition = Ints.bestSet(usize);
                for (Map.Entry<IntSet,IntSet> entry : range2domain.entrySet()) {
                    if (entry.getValue().size() == 1 && entry.getKey().size() == 1 && entry.getKey().min() == entry.getValue().min() * idenFactor) {
                        idenPartition.add(entry.getValue().min());
                    } else {
                        partsIter.add(entry.getValue());
                        otherColumns.add(entry.getKey());
                    }
                }
                if (!idenPartition.isEmpty())
                    partsIter.add(idenPartition);
            }
        }

        // refine based on the remaining columns
        for (IntSet otherCol : otherColumns) {
            refinePartitions(otherCol, arity - 1, range2domain);
        }
    }

    /**
     * Refines the atomic partitions this.parts based on the contents of the given
     * set.
     *
     * @requires all disj s, q: this.parts[int] | some s.ints && some q.ints && (no
     *           s.ints & q.ints) && this.parts[int].ints =
     *           [0..this.bounds.universe.size())
     * @ensures all disj s, q: this.parts'[int] | some s.ints && some q.ints && (no
     *          s.ints & q.ints) && this.parts'[int].ints =
     *          [0..this.bounds.universe.size()) && (all i: [0..this.parts'.size())
     *          | this.parts'[i].ints in set.ints || no this.parts'[i].ints &
     *          set.ints)
     */
    private void refinePartitions(IntSet set) {
        for (ListIterator<IntSet> partsIter = parts.listIterator(); partsIter.hasNext();) {
            IntSet part = partsIter.next();
            IntSet intersection = Ints.bestSet(part.min(), part.max());
            intersection.addAll(part);
            intersection.retainAll(set);
            if (!intersection.isEmpty() && intersection.size() < part.size()) {
                part.removeAll(intersection);
                partsIter.add(intersection);
            }
        }
    }

    /**
     * Returns an IntSet that can store elements in the range [0..size), and that
     * holds the given number.
     *
     * @requries 0 <= num < size
     * @return {s: IntSet | s.ints = num }
     */
    private static final IntSet oneOf(int size, int num) {
        final IntSet set = Ints.bestSet(size);
        set.add(num);
        return set;
    }
}
