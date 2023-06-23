/*
 * Kodkod -- Copyright (c) 2005-present, Emina Torlak
 * Pardinus -- Copyright (c) 2013-present, Nuno Macedo, INESC TEC
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
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */
package kodkod.instance;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import kodkod.ast.ConstantExpression;
import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.IntConstant;
import kodkod.ast.NaryFormula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.fol2sat.RelationCollector;
import kodkod.util.ints.IntSet;
import kodkod.util.ints.Ints;
import kodkod.util.ints.SparseSequence;
import kodkod.util.ints.TreeSequence;

/**
 * Represents a model (an instance) of a relational formula, which is a mapping
 * from {@link kodkod.ast.Relation relations} and integers to {@link kodkod.instance.TupleSet sets of tuples}
 * drawn from a given {@link kodkod.instance.Universe universe}.
 * 
 * @specfield universe: Universe
 * @specfield relations: set Relation
 * @specfield tuples: (relations -> one TupleSet) + (int -> lone TupleSet)
 * @invariant all r: tuples.TupleSet & Relation | r.arity = tuples[r].arity && tuples[r].universe = universe
 * @invariant all i: tuples.TupleSet & int | ints[i].arity = 1 && ints[i].size() = 1 
 * 
 * @author Emina Torlak
 * @modified Nuno Macedo // [HASLab] temporal model finding
 */
// [HASLab] removed final
public class Instance implements Cloneable {
	private final Map<Relation, TupleSet> tuples;
	private final SparseSequence<TupleSet> ints;
	private final Universe universe;
	
	// [HASLab] protected constructor
	protected Instance(Universe u, Map<Relation, TupleSet> tuples, SparseSequence<TupleSet> ints) {
		this.universe = u;
		this.tuples = tuples;
		this.ints = ints;
	}
	
	/**
	 * Constructs an empty instance over the given universe
	 * 
	 * @ensures this.universe' = universe && no this.tuples' 
	 * @throws NullPointerException  universe = null
	 */
	public Instance(final Universe universe) {
		if (universe==null) throw new NullPointerException("universe=null");
		this.universe = universe;
		this.tuples = new LinkedHashMap<Relation, TupleSet>();
		this.ints = new TreeSequence<TupleSet>();
	}
	
	/**
	 * Returns the universe from which the tuples in this instance
	 * are drawn.
	 * @return this.universe
	 */
	public Universe universe() {
		return universe;
	}
	
	/** 
	 * Returns true if this instance maps the given relation to a set
	 * of tuples; otherwise returns false.
	 * @return r in this.relations
	 */
	public boolean contains(Relation relation) {
		return tuples.containsKey(relation);
	}
	
	/**
	 * Returns true if this instance maps the given integer to a singleton
	 * tupleset; otherwise returns false.
	 * @return some this.tuples[i]
	 */
	public boolean contains(int i) {
		return ints.containsIndex(i);
	}
	
	/**
	 * Returns the relations mapped by this instance.  The returned set
	 * does not support addition.  It supports remval if this is not an
	 * unmodifiable instance.
	 * @return this.relations
	 */
	public Set<Relation> relations() {
		return tuples.keySet();
	}
	
	/**
	 * Returns the integers mapped by this instance.  The returned set 
	 * does not support addition.  It supports remval if this is not an
	 * unmodifiable instance.
	 * @return this.ints.TupleSet
	 */
	public IntSet ints() { 
		return ints.indices();
	}
	
	/**
	 * Maps the given relation to the given tuple set.  
	 * @ensures this.tuples' = this.tuples ++ relation->s
	 * @throws NullPointerException  relation = null || s = null
	 * @throws IllegalArgumentException  relation.arity != s.arity
	 * @throws IllegalArgumentException  s.universe != this.universe
	 * @throws UnsupportedOperationException  this is an unmodifiable instance
	 */
	public void add(final Relation relation, TupleSet s) {
		if (!s.universe().equals(universe))
			throw new IllegalArgumentException("s.universe!=this.universe");
		if (relation.arity()!=s.arity())
			throw new IllegalArgumentException("relation.arity!=s.arity");
		tuples.put(relation, s.clone().unmodifiableView());
	}

	/**
	 * Maps the given integer to the given tuple set.  
	 * @ensures this.tuples' = this.tuples ++ i->s
	 * @throws NullPointerException  s = null
	 * @throws IllegalArgumentException  s.arity != 1 || s.size() != 1
	 * @throws IllegalArgumentException  s.universe != this.universe
	 * @throws UnsupportedOperationException  this is an unmodifiable instance
	 */
	public void add(int i, TupleSet s) {
		if (!s.universe().equals(universe))
			throw new IllegalArgumentException("s.universe!=this.universe");
		if (s.arity()!=1)
			throw new IllegalArgumentException("s.arity!=1: " + s);
		if (s.size()!=1)
			throw new IllegalArgumentException("s.size()!=1: " + s);
		ints.put(i, s.clone().unmodifiableView());
	}
	
	/**
	 * Returns the set of tuples assigned to the given relation by this Instance.
	 * If the relation is not mapped by the model, null is returned.
	 * 
	 * @return this.tuples[relation]
	 */
	public TupleSet tuples(Relation relation) {
		return tuples.get(relation);
	}
	
	// [AlloyTools]
    public TupleSet tuples(String relationName) {
        Relation rel = findRelationByName(relationName);
        if (rel == null)
            return null;
        return tuples(rel);
    }

	// [AlloyTools]
    public Relation findRelationByName(String relationName) {
        for (Relation rel : relations())
            if (rel.name().equals(relationName))
                return rel;
        return null;
    }
	/**
	 * Returns a map view of Relation<:this.tuples.  The returned map is unmodifiable.
	 * @return a map view of Relation<:this.tuples.  
	 */
	public Map<Relation, TupleSet> relationTuples() {
		return Collections.unmodifiableMap(tuples);
	}
	
	/**
	 * Returns the set of tuples assigned to the given integer by this Instance.
	 * If the integer is not mapped by the model, null is returned.
	 * 
	 * @return this.tuples[i]
	 */
	public TupleSet tuples(int i) {
		return ints.get(i);
	}
	
	/**
	 * Returns a sparse sequence view of int<:this.tuples.  The returned sequence is unmodifiable.
	 * @return a sparse sequence view of int<:this.tuples.
	 */
	public SparseSequence<TupleSet> intTuples() {
		return Ints.unmodifiableSequence(ints);
	}
	
	/**
	 * Returns an unmodifiable view of this instance.
	 * @return an unmodifiable view of this instance.
	 */
	public Instance unmodifiableView() {
		return new Instance(universe, Collections.unmodifiableMap(tuples),  Ints.unmodifiableSequence(ints));
	}
	
	/**
	 * Returns a deep copy of this Instance object.
	 * @return a deep copy of this Instance object.
	 */
	public Instance clone() {
		try {
			return new Instance(universe, new LinkedHashMap<Relation, TupleSet>(tuples), ints.clone());
		} catch (CloneNotSupportedException cnse) {
			throw new InternalError(); // should not be reached
		}
	}
	

	/**
	 * Converts an instance into a formula that exactly identifies it. Requires that
	 * every relevant atom be reified into a singleton relation or quantified in a
	 * some-disj pattern, which may be re-used between calls. Relevant atoms are
	 * determined from the provided formulas.
	 * 
	 * Will change <bounds> if not all atoms of the universe are present at <reif>
	 * and <someDisj> false.
	 * 
	 * @assumes reif != null
	 * @assumes !someDisj => bounds != null
	 * @param reif the previously reified atoms, as relations or quantified vars depending on <someDisj>
	 * @param formula a formula from which the relevant relations are identified
	 * @param someDisj whether the formula will use atoms reified as relations or a some-disj pattern
	 * @param bounds the problem's bounds, updated if !someDisj 
	 * @throws NullPointerException reif = null
	 * @throws NullPointerException !someDisj && bounds == null
	 * @return the formula representing <this>
	 */
	public Formula formulate(Map<Object, Expression> reif, Formula formula, boolean someDisj, Bounds bounds) {
		return formulate(reif,formula,someDisj,bounds,false);
	}
	
	/**
	 * Converts an instance into a formula that exactly identifies it. Requires that
	 * every relevant atom be reified into a singleton relation or quantified in a
	 * some-disj pattern, which may be re-used between calls. Relevant atoms are
	 * determined from the provided formulas.
	 * 
	 * Will change <bounds> if not all atoms of the universe are present at <reif>
	 * and <someDisj> false.
	 * 
 	 * NOTE: the <bounds> representing the instance contain a universe that is not
	 * the one of the original problem; thus, local universe restrictions will only
	 * consider those atoms.
	 * @assumes reif != null
	 * @assumes !someDisj => bounds != null
	 * @param reif the previously reified atoms, as relations or quantified vars depending on <someDisj>
	 * @param formula a formula from which the relevant relations are identified
	 * @param someDisj whether the formula will use atoms reified as relations or a some-disj pattern
	 * @param bounds the problem's bounds, updated if !someDisj 
	 * @param localUniv whether to restrict the universe of atoms locally, only relevant if some-disj pattern
	 * @throws NullPointerException reif = null
	 * @throws NullPointerException !someDisj && bounds == null
	 * @return the formula representing <this>
	 */
	// [HASLab]
	public Formula formulate(Map<Object, Expression> reif, Formula formula, boolean someDisj, Bounds bounds, boolean localUniv) {
		
		Set<Relation> relevants = formula.accept(new RelationCollector(new HashSet<>()));
		// reify atoms not yet reified
		for (int i = 0; i < universe().size(); i++) {
			// integers do not need to be quantified
			if (!universe().atom(i).toString().matches("-?\\d+")) {
				Expression r;
				if (reif.keySet().contains(universe().atom(i)))
					r = reif.get(universe().atom(i));
				else {
					if (someDisj) {
						r = Variable.unary(universe().atom(i).toString());
					} else {
						r = Relation.atom(universe().atom(i).toString());
					}
					reif.put(universe().atom(i), r);
				}
				if (!someDisj && !bounds.relations.contains(r))
					bounds.boundExactly((Relation) r, bounds.universe().factory().setOf(universe().atom(i)));
			}
		}

		List<Expression> locals = new ArrayList<Expression>();

		// create an equality for every relation
		// a = A + ... && r = A -> B + ... 
		List<Formula> res = new ArrayList<Formula>();
		for (Relation rel : tuples.keySet()) {
			// do not translate relations from reified from atoms
			if (rel.isAtom() || (relevants != null && !relevants.contains(rel)))
				continue;

			TupleSet tset = tuples.get(rel);
			Iterator<Tuple> it = tset.iterator();

			Expression r;
			if (it.hasNext()) {
				Tuple u = it.next();
				Expression r1 = reif.get(u.atom(0));
				locals.add(r1);
				for (int i = 1; i < u.arity(); i++)
					r1 = r1.product(reif.get(u.atom(i)));
				r = r1;
			} else {
				r = ConstantExpression.NONE;
				for (int i = 1; i < tset.arity(); i++)
					r = r.product(ConstantExpression.NONE);
			}

			while (it.hasNext()) {
				Tuple u = it.next();
				Expression r1 = reif.get(u.atom(0));
				locals.add(r1);
				for (int i = 1; i < u.arity(); i++)
					r1 = r1.product(reif.get(u.atom(i)));
				r = r.union(r1);
			}
			res.add(rel.eq(r));
		}
		
		if (someDisj && localUniv) {
			Expression al = null;
			for (Expression e : locals)
				al = al == null? e : al.union(e);
			for (int i = 0; i < universe().size(); i++)
				if (universe().atom(i).toString().matches("-?\\d+")) {
					Expression intexp = IntConstant.constant(Integer.valueOf(universe().atom(i).toString())).toExpression();
					al = al == null ? intexp : al.union(intexp);
				}
			res.add(al.eq(Expression.UNIV));
		}
		
		return NaryFormula.and(res);
	}

	/**
	 * {@inheritDoc}
	 * @see java.lang.Object#toString()
	 */
	public String toString() {
		return "relations: "+tuples.toString() + "\nints: " + ints;
	}
	
}

