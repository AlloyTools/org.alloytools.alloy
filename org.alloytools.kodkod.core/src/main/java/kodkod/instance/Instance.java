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

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import kodkod.ast.Relation;
import kodkod.util.ints.IntSet;
import kodkod.util.ints.Ints;
import kodkod.util.ints.SparseSequence;
import kodkod.util.ints.TreeSequence;

/**
 * Represents a model (an instance) of a relational formula, which is a mapping
 * from {@link kodkod.ast.Relation relations} and integers to
 * {@link kodkod.instance.TupleSet sets of tuples} drawn from a given
 * {@link kodkod.instance.Universe universe}.
 *
 * @specfield universe: Universe
 * @specfield relations: set Relation
 * @specfield tuples: (relations -> one TupleSet) + (int -> lone TupleSet)
 * @invariant all r: tuples.TupleSet & Relation | r.arity = tuples[r].arity &&
 *            tuples[r].universe = universe
 * @invariant all i: tuples.TupleSet & int | ints[i].arity = 1 && ints[i].size()
 *            = 1
 * @author Emina Torlak
 */
public final class Instance implements Cloneable {

    private final Map<Relation,TupleSet>   tuples;
    private final SparseSequence<TupleSet> ints;
    private final Universe                 universe;

    private Instance(Universe u, Map<Relation,TupleSet> tuples, SparseSequence<TupleSet> ints) {
        if (u == null)
            throw new NullPointerException("universe=null");
        this.universe = u;
        this.tuples = tuples;
        this.ints = ints;
    }

    /**
     * Constructs an empty instance over the given universe
     *
     * @ensures this.universe' = universe && no this.tuples'
     * @throws NullPointerException universe = null
     */
    public Instance(final Universe universe) {
        this(universe, new LinkedHashMap<Relation,TupleSet>(), new TreeSequence<TupleSet>());
    }

    /**
     * Returns the universe from which the tuples in this instance are drawn.
     *
     * @return this.universe
     */
    public Universe universe() {
        return universe;
    }

    /**
     * Returns true if this instance maps the given relation to a set of tuples;
     * otherwise returns false.
     *
     * @return r in this.relations
     */
    public boolean contains(Relation relation) {
        return tuples.containsKey(relation);
    }

    /**
     * Returns true if this instance maps the given integer to a singleton tupleset;
     * otherwise returns false.
     *
     * @return some this.tuples[i]
     */
    public boolean contains(int i) {
        return ints.containsIndex(i);
    }

    /**
     * Returns the relations mapped by this instance. The returned set does not
     * support addition. It supports remval if this is not an unmodifiable instance.
     *
     * @return this.relations
     */
    public Set<Relation> relations() {
        return tuples.keySet();
    }

    public Collection<Relation> skolems() {
        Set<Relation> rels = relations();
        ArrayList<Relation> ans = new ArrayList<Relation>(rels.size());
        for (Relation r : rels)
            if (r.isSkolem())
                ans.add(r);
        return ans;
    }

    /**
     * Returns the integers mapped by this instance. The returned set does not
     * support addition. It supports remval if this is not an unmodifiable instance.
     *
     * @return this.ints.TupleSet
     */
    public IntSet ints() {
        return ints.indices();
    }

    /**
     * Maps the given relation to the given tuple set.
     *
     * @ensures this.tuples' = this.tuples ++ relation->s
     * @throws NullPointerException relation = null || s = null
     * @throws IllegalArgumentException relation.arity != s.arity
     * @throws IllegalArgumentException s.universe != this.universe
     * @throws UnsupportedOperationException this is an unmodifiable instance
     */
    public void add(final Relation relation, TupleSet s) {
        if (!s.universe().equals(universe))
            throw new IllegalArgumentException("s.universe!=this.universe");
        if (relation.arity() != s.arity())
            throw new IllegalArgumentException("relation.arity!=s.arity");
        TupleSet val = s.clone().unmodifiableView();
        tuples.put(relation, val);
    }

    /**
     * Maps the given integer to the given tuple set.
     *
     * @ensures this.tuples' = this.tuples ++ i->s
     * @throws NullPointerException s = null
     * @throws IllegalArgumentException s.arity != 1 || s.size() != 1
     * @throws IllegalArgumentException s.universe != this.universe
     * @throws UnsupportedOperationException this is an unmodifiable instance
     */
    public void add(int i, TupleSet s) {
        if (!s.universe().equals(universe))
            throw new IllegalArgumentException("s.universe!=this.universe");
        if (s.arity() != 1)
            throw new IllegalArgumentException("s.arity!=1: " + s);
        if (s.size() != 1)
            throw new IllegalArgumentException("s.size()!=1: " + s);
        ints.put(i, s.clone().unmodifiableView());
    }

    /**
     * Returns the set of tuples assigned to the given relation by this Instance. If
     * the relation is not mapped by the model, null is returned.
     *
     * @return this.tuples[relation]
     */
    public TupleSet tuples(Relation relation) {
        return tuples.get(relation);
    }

    public TupleSet tuples(String relationName) {
        Relation rel = findRelationByName(relationName);
        if (rel == null)
            return null;
        return tuples(rel);
    }

    public Relation findRelationByName(String relationName) {
        for (Relation rel : relations())
            if (rel.name().equals(relationName))
                return rel;
        return null;
    }

    /**
     * Returns a map view of Relation<:this.tuples. The returned map is
     * unmodifiable.
     *
     * @return a map view of Relation<:this.tuples.
     */
    public Map<Relation,TupleSet> relationTuples() {
        return Collections.unmodifiableMap(tuples);
    }

    /**
     * Returns the set of tuples assigned to the given integer by this Instance. If
     * the integer is not mapped by the model, null is returned.
     *
     * @return this.tuples[i]
     */
    public TupleSet tuples(int i) {
        return ints.get(i);
    }

    /**
     * Returns a sparse sequence view of int<:this.tuples. The returned sequence is
     * unmodifiable.
     *
     * @return a sparse sequence view of int<:this.tuples.
     */
    public SparseSequence<TupleSet> intTuples() {
        return Ints.unmodifiableSequence(ints);
    }

    /**
     * Returns an unmodifiable view of this instance.
     *
     * @return an unmodifiable view of this instance.
     */
    public Instance unmodifiableView() {
        return new Instance(universe, Collections.unmodifiableMap(tuples), Ints.unmodifiableSequence(ints));
    }

    /**
     * Returns a deep copy of this Instance object.
     *
     * @return a deep copy of this Instance object.
     */
    @Override
    public Instance clone() {
        try {
            return new Instance(universe, new LinkedHashMap<Relation,TupleSet>(tuples), ints.clone());
        } catch (CloneNotSupportedException cnse) {
            throw new InternalError(); // should not be reached
        }
    }

    /**
     * {@inheritDoc}
     *
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        return "relations: " + tuples.toString() + "\nints: " + ints;
    }

    public String toPrettyString() {
        StringBuilder sb = new StringBuilder();
        for (Relation r : relations()) {
            TupleSet val = tuples(r);
            sb.append(r.name()).append(" = [").append(val.size()).append("] ").append(val).append("\n");
        }
        return sb.toString();
    }
}
