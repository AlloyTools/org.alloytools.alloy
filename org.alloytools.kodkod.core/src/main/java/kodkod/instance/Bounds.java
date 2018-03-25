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
package kodkod.instance;

import static java.util.Collections.unmodifiableMap;
import static kodkod.util.ints.Ints.unmodifiableSequence;

import java.util.AbstractSet;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import kodkod.ast.Expression;
import kodkod.ast.IntConstant;
import kodkod.ast.Relation;
import kodkod.util.ints.IntSet;
import kodkod.util.ints.SparseSequence;
import kodkod.util.ints.TreeSequence;

/**
 * <p>
 * A Bounds object maps a {@link kodkod.ast.Relation relation} <i>r</i> to two
 * {@link kodkod.instance.TupleSet sets of tuples}, <i>rL</i> and <i>rU</i>,
 * which represent the lower and upper bounds on the
 * {@link kodkod.instance.Tuple set of tuples} to which an
 * {@link kodkod.instance.Instance instance} based on these bounds may map
 * <i>r</i>. The set <i>rL</i> represents all the tuples that a given relation
 * <i>must</i> contain. The set <i>rU</i> represents all the tuples that a
 * relation <i>may</i> contain. All bounding sets range over the same
 * {@link kodkod.instance.Universe universe}.
 * </p>
 * <p>
 * A Bounds object also maps integers to singleton tupleset that represent them.
 * A tupleset may represent more than one integer, but an integer is represented
 * by at most one tupleset.
 * </p>
 *
 * @specfield universe: Universe
 * @specfield relations: set Relation
 * @specfield intBound: int -> lone TupleSet
 * @specfield lowerBound: relations -> one TupleSet
 * @specfield upperBound: relations -> one TupleSet
 * @invariant all i: intBound.TupleSet | intBound[i].size() = 1 &&
 *            intBound[i].arity() = 1
 * @invariant lowerBound[relations].universe = upperBound[relations].universe =
 *            universe
 * @invariant all r: relations | lowerBound[r].arity = upperBound[r].arity =
 *            r.arity
 * @invariant all r: relations | lowerBound[r].tuples in upperBound[r].tuples
 * @author Emina Torlak
 **/
public final class Bounds implements Cloneable {

    private final TupleFactory             factory;
    private final Map<Relation,TupleSet>   lowers, uppers;
    private final SparseSequence<TupleSet> intbounds;
    private final Set<Relation>            relations;
    private final Map<Object,Relation>     atom2rel;

    /**
     * Constructs a Bounds object with the given factory and mappings.
     */
    private Bounds(TupleFactory factory, Map<Relation,TupleSet> lower, Map<Relation,TupleSet> upper, SparseSequence<TupleSet> intbounds) {
        this.factory = factory;
        this.lowers = lower;
        this.uppers = upper;
        this.intbounds = intbounds;
        this.relations = relations(lowers, uppers);
        this.atom2rel = new HashMap<Object,Relation>();
        for (Entry<Relation,TupleSet> e : uppers.entrySet()) {
            addAtomRel(e.getKey(), e.getValue());
        }
    }

    /**
     * Constructs new Bounds over the given universe.
     *
     * @ensures this.universe' = universe && no this.relations' && no this.intBound'
     * @throws NullPointerException universe = null
     */
    public Bounds(Universe universe) {
        this.factory = universe.factory();
        this.lowers = new LinkedHashMap<Relation,TupleSet>();
        this.uppers = new LinkedHashMap<Relation,TupleSet>();
        this.intbounds = new TreeSequence<TupleSet>();
        this.relations = relations(lowers, uppers);
        this.atom2rel = new HashMap<Object,Relation>();
    }

    /**
     * Returns a set view of the relations mapped by the given lower/upper bounds.
     *
     * @requires lowers.keySet().equals(uppers.keySet())
     * @return a set view of the relations mapped by the given lower/upper bounds
     */
    private static Set<Relation> relations(final Map<Relation,TupleSet> lowers, final Map<Relation,TupleSet> uppers) {
        return new AbstractSet<Relation>() {

            @Override
            public Iterator<Relation> iterator() {
                return new Iterator<Relation>() {

                    final Iterator<Relation> itr  = uppers.keySet().iterator();
                    Relation                 last = null;

                    @Override
                    public boolean hasNext() {
                        return itr.hasNext();
                    }

                    @Override
                    public Relation next() {
                        return last = itr.next();
                    }

                    @Override
                    public void remove() {
                        itr.remove();
                        lowers.remove(last);
                    }
                };
            }

            @Override
            public int size() {
                return uppers.size();
            }

            @Override
            public boolean contains(Object key) {
                return uppers.containsKey(key);
            }

            @Override
            public boolean remove(Object key) {
                return (uppers.remove(key) != null) && (lowers.remove(key) != null);
            }

            @Override
            public boolean removeAll(Collection< ? > c) {
                return uppers.keySet().removeAll(c) && lowers.keySet().removeAll(c);
            }

            @Override
            public boolean retainAll(Collection< ? > c) {
                return uppers.keySet().retainAll(c) && lowers.keySet().retainAll(c);
            }
        };
    }

    /**
     * Returns this.universe.
     *
     * @return this.universe
     */
    public Universe universe() {
        return factory.universe();
    }

    /**
     * Returns the set of all relations bound by this Bounds. The returned set does
     * not support the add operation. It supports removal iff this is not an
     * unmodifiable Bounds.
     *
     * @return this.relations
     */
    public Set<Relation> relations() {
        return relations;
    }

    public Collection<Relation> skolems() {
        ArrayList<Relation> ans = new ArrayList<Relation>(relations.size());
        for (Relation r : relations)
            if (r.isSkolem())
                ans.add(r);
        return ans;
    }

    public Collection<Relation> varRels() {
        ArrayList<Relation> ans = new ArrayList<Relation>(relations.size());
        TupleSet ub, lb;
        for (Relation r : relations) {
            ub = uppers.get(r);
            lb = lowers.get(r);
            if (ub.size() > lb.size())
                ans.add(r);
        }
        return ans;
    }

    /**
     * Returns the set of all integers bound by this Bounds. The returned set does
     * not support the add operation. It supports removal iff this is not an
     * unmodifiable Bounds.
     *
     * @return this.intBounds.TupleSet
     */
    public IntSet ints() {
        return intbounds.indices();
    }

    /**
     * Returns the set of tuples that r must contain (the lower bound on r's
     * contents). If r is not mapped by this, null is returned.
     *
     * @return r in this.relations => lowerBound[r], null
     */
    public TupleSet lowerBound(Relation r) {
        return lowers.get(r);
    }

    /**
     * Returns a map view of this.lowerBound. The returned map is not modifiable.
     *
     * @return a map view of this.lowerBound
     */
    public Map<Relation,TupleSet> lowerBounds() {
        return unmodifiableMap(lowers);
    }

    /**
     * Returns the set of tuples that r may contain (the upper bound on r's
     * contents). If r is not mapped by this, null is returned.
     *
     * @return r in this.relations => upperBound[r], null
     */
    public TupleSet upperBound(Relation r) {
        return uppers.get(r);
    }

    /**
     * Returns a map view of this.upperBound. The returned map is not modifiable.
     *
     * @return a map view of this.upperBound
     */
    public Map<Relation,TupleSet> upperBounds() {
        return unmodifiableMap(uppers);
    }

    /**
     * Returns the set of tuples representing the given integer. If i is not mapped
     * by this, null is returned.
     *
     * @return this.intBound[i]
     */
    public TupleSet exactBound(int i) {
        return intbounds.get(i);
    }

    /**
     * Returns a sparse sequence view of this.intBound. The returned sequence is not
     * modifiable.
     *
     * @return a sparse sequence view of this.intBound
     */
    public SparseSequence<TupleSet> intBounds() {
        return unmodifiableSequence(intbounds);
    }

    /**
     * @throws IllegalArgumentException arity != bound.arity
     * @throws IllegalArgumentException bound.universe != this.universe
     */
    private void checkBound(int arity, TupleSet bound) {
        if (arity != bound.arity())
            throw new IllegalArgumentException("bound.arity != r.arity");
        if (!bound.universe().equals(factory.universe()))
            throw new IllegalArgumentException("bound.universe != this.universe");
    }

    /**
     * Sets both the lower and upper bounds of the given relation to the given set
     * of tuples.
     *
     * @requires tuples.arity = r.arity && tuples.universe = this.universe
     * @ensures this.relations' = this.relations + r this.lowerBound' =
     *          this.lowerBound' ++ r->tuples && this.upperBound' = this.lowerBound'
     *          ++ r->tuples
     * @throws NullPointerException r = null || tuples = null
     * @throws IllegalArgumentException tuples.arity != r.arity || tuples.universe
     *             != this.universe
     */
    public void boundExactly(Relation r, TupleSet tuples) {
        checkBound(r.arity(), tuples);
        final TupleSet unmodifiableTuplesCopy = tuples.clone().unmodifiableView();
        putBound(lowers, r, unmodifiableTuplesCopy);
        putBound(uppers, r, unmodifiableTuplesCopy);
    }

    /**
     * Sets the lower and upper bounds for the given relation.
     *
     * @requires lower.tuples in upper.tuples && lower.arity = upper.arity = r.arity
     *           && lower.universe = upper.universe = this.universe
     * @ensures this.relations' = this.relations + r && this.lowerBound' =
     *          this.lowerBound ++ r->lower && this.upperBound' = this.upperBound ++
     *          r->upper
     * @throws NullPointerException r = null || lower = null || upper = null
     * @throws IllegalArgumentException lower.arity != r.arity || upper.arity !=
     *             r.arity
     * @throws IllegalArgumentException lower.universe != this.universe ||
     *             upper.universe != this.universe
     * @throws IllegalArgumentException lower.tuples !in upper.tuples
     */
    public void bound(Relation r, TupleSet lower, TupleSet upper) {
        if (!upper.containsAll(lower))
            throw new IllegalArgumentException("lower.tuples !in upper.tuples");
        if (upper.size() == lower.size()) {
            // upper.containsAll(lower) && upper.size()==lower.size() =>
            // upper.equals(lower)
            boundExactly(r, lower);
        } else {
            checkBound(r.arity(), lower);
            checkBound(r.arity(), upper);
            putBound(lowers, r, lower.clone().unmodifiableView());
            putBound(uppers, r, upper.clone().unmodifiableView());
        }
    }

    /**
     * Makes the specified tupleset the upper bound on the contents of the given
     * relation. The lower bound automatically becomen an empty tupleset with the
     * same arity as the relation.
     *
     * @requires upper.arity = r.arity && upper.universe = this.universe
     * @ensures this.relations' = this.relations + r this.lowerBound' =
     *          this.lowerBound ++ r->{s: TupleSet | s.universe = this.universe &&
     *          s.arity = r.arity && no s.tuples} && this.upperBound' =
     *          this.upperBound ++ r->upper
     * @throws NullPointerException r = null || upper = null
     * @throws IllegalArgumentException upper.arity != r.arity || upper.universe !=
     *             this.universe
     */
    public void bound(Relation r, TupleSet upper) {
        checkBound(r.arity(), upper);
        putBound(lowers, r, factory.noneOf(r.arity()).unmodifiableView());
        putBound(uppers, r, upper.clone().unmodifiableView());
    }

    /**
     * Makes the specified tupleset an exact bound on the relational value that
     * corresponds to the given integer.
     *
     * @requires ibound.arity = 1 && i.bound.size() = 1
     * @ensures this.intBound' = this.intBound' ++ i -> ibound
     * @throws NullPointerException ibound = null
     * @throws IllegalArgumentException ibound.arity != 1 || ibound.size() != 1
     * @throws IllegalArgumentException ibound.universe != this.universe
     */
    public void boundExactly(int i, TupleSet ibound) {
        checkBound(1, ibound);
        if (ibound.size() != 1)
            throw new IllegalArgumentException("ibound.size != 1: " + ibound);
        intbounds.put(i, ibound.clone().unmodifiableView());
    }

    /**
     * Creates atom relations for all atoms present in this Bounds for which
     * corresponding atom relations don't already exist.
     */
    public void ensureAtomRelations() {
        for (Object atom : universe()) {
            if (getAtomExpr(atom, atom2rel) == null) {
                Relation ar = Relation.atom(atom.toString());
                boundExactly(ar, factory.setOf(atom));
            }
            ;
        }
    }

    public Expression ts2expr(TupleSet tset) {
        if (tset == null)
            return Expression.NONE;
        Expression tsetExpr = null;
        for (Tuple t : tset) {
            Expression tupleExpr = null;
            for (int i = 0; i < t.arity(); i++) {
                Expression atomRel = ensureAtomExpr(t.atom(i));
                tupleExpr = tupleExpr == null ? atomRel : tupleExpr.product(atomRel);
            }
            tsetExpr = tsetExpr == null ? tupleExpr : tsetExpr.union(tupleExpr);
        }
        return (tsetExpr == null) ? Expression.NONE : tsetExpr;
    }

    public static Expression getAtomExpr(Object atom, Map<Object,Relation> atom2rel) {
        if (atom instanceof Integer)
            return IntConstant.constant((Integer) atom).toExpression();
        if (atom instanceof String) {
            try {
                return IntConstant.constant(Integer.parseInt(atom.toString())).toExpression();
            } catch (NumberFormatException e) {}
        }
        Relation rel = atom2rel != null ? atom2rel.get(atom) : null;
        return rel;
    }

    /**
     * Returns an unmodifiable view of this Bounds object.
     *
     * @return an unmodifiable view of his Bounds object.
     */
    public Bounds unmodifiableView() {
        return new Bounds(factory, unmodifiableMap(lowers), unmodifiableMap(uppers), unmodifiableSequence(intbounds));
    }

    /**
     * Returns a deep (modifiable) copy of this Bounds object.
     *
     * @return a deep (modifiable) copy of this Bounds object.
     */
    @Override
    public Bounds clone() {
        try {
            return new Bounds(factory, new LinkedHashMap<Relation,TupleSet>(lowers), new LinkedHashMap<Relation,TupleSet>(uppers), intbounds.clone());
        } catch (CloneNotSupportedException cnse) {
            throw new InternalError(); // should not be reached
        }
    }

    /**
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        final StringBuilder str = new StringBuilder();
        str.append("relation bounds:");
        for (Map.Entry<Relation,TupleSet> entry : lowers.entrySet()) {
            TupleSet upper = uppers.get(entry.getKey());
            str.append("\n ");
            str.append(entry.getKey());
            str.append(": (").append(entry.getValue().size()).append(", ").append(upper.size()).append(") :");
            str.append(": [");
            str.append(entry.getValue());
            if (!upper.equals(entry.getValue())) {
                str.append(", ");
                str.append(upper);
            }
            str.append("]");
        }
        str.append("\nint bounds: ");
        str.append("\n ");
        str.append(intbounds);
        return str.toString();
    }

    private void putBound(Map<Relation,TupleSet> map, Relation r, TupleSet tset) {
        map.put(r, tset);
        if (r.isAtom() && System.identityHashCode(map) == System.identityHashCode(uppers))
            addAtomRel(r, tset);
    }

    private void addAtomRel(Relation rel, TupleSet val) {
        if (!rel.isAtom())
            return;
        assert val.size() == 1 : String.format("atom relation '%s' evaluates to more than one tuple: %s", rel, val);
        assert val.arity() == 1 : String.format("atom relation '%s' evaluates to a non-unary tuple set: %s", rel, val);
        atom2rel.put(val.iterator().next().atom(0), rel);
    }

    private Expression ensureAtomExpr(Object atom) {
        Expression ans = getAtomExpr(atom, atom2rel);
        if (ans == null)
            throw new InternalError("No relation found for atom '" + atom + "'");
        return ans;
    }

    public Relation findRelByName(String name) {
        for (Relation r : relations())
            if (r.name().equals(name))
                return r;
        return null;
    }

}
