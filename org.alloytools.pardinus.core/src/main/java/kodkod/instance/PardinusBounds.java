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
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */
package kodkod.instance;

import static java.util.Collections.unmodifiableMap;
import static kodkod.util.ints.Ints.unmodifiableSequence;

import java.util.AbstractSet;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import kodkod.ast.ConstantExpression;
import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.NaryFormula;
import kodkod.ast.Node;
import kodkod.ast.Relation;
import kodkod.engine.Evaluator;
import kodkod.engine.Solution;
import kodkod.engine.config.Reporter;
import kodkod.engine.fol2sat.RelationCollector;
import kodkod.engine.ltl2fol.TemporalTranslator;
import kodkod.engine.fol2sat.ComplRelationReplacer;
import kodkod.util.ints.SparseSequence;

/**
 * A structure representing the bounds of a temporal model finding problem, that
 * are used to embody partial knowledge about the problem. These temporal bounds
 * are essentially a stream (i.e., infinite sequence) of regular bounds. To be
 * encoded into a finite structure, it is modeled as a finite prefix with a loop
 * pointing to a previous position. Thus, a temporal bound can be used to bind
 * problems with an arbitrary number of states by unrolling the stream. Note
 * that the actual number of states used by the model finder to solve the
 * temporal problem is not known at the time of bound definition. The bounds of
 * static (non-variable) need only be defined once since they do not vary from
 * state to state.
 * 
 * If these temporal bounds are treated like regular bounds (i.e., without ever
 * moving the iterator), then those bounds are applied to every state in the
 * model finding problem (since there is only one position pointing to itself
 * through the loop), behaving as expected from regular bounds.
 * 
 * The same set of variable relations should be bound by every position of the
 * bound trace, otherwise the solving procedure will fail.
 * 
 * Adapted from {@link kodkod.instance.Bounds}.
 * 
 * @author Nuno Macedo // [HASLab] temporal, decomposed, symbolic model finding
 * @author Tiago Guimarães, Nuno Macedo // [HASLab] target-oriented model
 *         finding
 */
public class PardinusBounds extends Bounds {
	
	private final Set<Relation> relations_all;

	/* Symbolic bounds */

	private final Map<Relation, Expression> lowers_symb;
	private final Map<Relation, Expression> uppers_symb;
	private final Set<Relation> relations_symb;

	/* Target-oriented bounds */

	private final Map<Relation, TupleSet> targets;
	private final Map<Relation, Integer> weights;

	/* Decomposed bounds */

	public boolean integrated;
	public PardinusBounds amalgamated;
	public boolean trivial_config;
	
	/** Statistics, how many times has this bound been integrated. */
	public int integration = 0;
	
	/**
	 * Constructs new empty bounds over the given universe.
	 * 
	 * @param universe the atom universe
	 * @ensures this.universe' = universe && no this.relations' && no
	 *          this.intBound'
	 * @throws NullPointerException
	 *             universe = null
	 */
	public PardinusBounds(Universe universe) {
		super(universe);
		this.targets = new LinkedHashMap<Relation, TupleSet>();
		this.weights = new LinkedHashMap<Relation, Integer>();
		this.amalgamated = null;
		this.trivial_config = false;
		this.integrated = false;
		this.lowers_symb = new LinkedHashMap<Relation, Expression>();
		this.uppers_symb = new LinkedHashMap<Relation, Expression>();
		this.relations_all = relations(lowers, lowers_symb, uppers, uppers_symb);
		this.relations_symb = relations(lowers_symb, uppers_symb);
		this.symbolic = new SymbolicStructures();
	}

	/**
	 * Constructs new complete bounds over the given universe.
	 * 
	 * @ensures this.universe' = universe && no this.relations' && no
	 *          this.intBound' && ...
	 * @throws NullPointerException
	 *             universe = null
	 */
	private PardinusBounds(TupleFactory factory,
			Map<Relation, TupleSet> lower, Map<Relation, TupleSet> upper,
			Map<Relation, TupleSet> target, Map<Relation, Integer> weights,
			Map<Relation, Expression> lowers_s,
			Map<Relation, Expression> uppers_s, SymbolicStructures symbolic,
			SparseSequence<TupleSet> intbounds, PardinusBounds amalg,
			boolean integrated, boolean trivial_config, int integration) {
		super(factory, lower, upper, intbounds);
		this.targets = target;
		this.weights = weights;
		this.amalgamated = amalg;
		this.trivial_config = trivial_config;
		this.integrated = integrated;
		this.lowers_symb = lowers_s;
		this.uppers_symb = uppers_s;
		this.symbolic = new SymbolicStructures(symbolic.reif,symbolic.dereif,symbolic.deps,symbolic.compls);
		this.relations_all = relations(lowers, lowers_symb, uppers, uppers_symb);
		this.relations_symb = relations(lowers_symb, uppers_symb);
		this.integration = integration;
	}

	/**
	 * Constructor for decomposed bounds. The first is the partial problem
	 * (which will be embedded in <this>) and the second is amalgamated with the
	 * first in amalgamated. Non-mergeable data is selected from <partial>.
	 * 
	 * @param partial the partial problem bounds
	 * @param remainder the remainder bounds
	 */
	public PardinusBounds(PardinusBounds partial, Bounds remainder) {
		this(partial.universe().factory(), partial.lowers, partial.uppers, partial.targets,
				partial.weights, partial.lowers_symb, partial.uppers_symb, partial.symbolic, partial.intBounds(), null,
				partial.integrated, partial.trivial_config,partial.integration);

		this.amalgamated = partial.clone();
		this.amalgamated.merge(remainder);
	}
	
	/**
	 * Automatic partition of exiting bounds into static/relation bounds.
	 * 
	 * @param bounds the original, non-decomposed bounds
	 * @return the bounds split between static and mutable relations
	 */
	static public PardinusBounds splitAtTemporal(PardinusBounds bounds) {
		// Create a new bound with static information
		PardinusBounds b = new PardinusBounds(bounds.universe().factory(), 
				new HashMap<Relation, TupleSet>(bounds.lowers), new HashMap<Relation, TupleSet>(bounds.uppers),
				new HashMap<Relation, TupleSet>(bounds.targets), new HashMap<Relation, Integer>(bounds.weights), 
				new HashMap<Relation, Expression>(bounds.lowers_symb), new HashMap<Relation, Expression>(bounds.uppers_symb),
				bounds.symbolic, bounds.intBounds(), null, bounds.integrated,
				bounds.trivial_config, bounds.integration);
		// TODO: is it problematic to use the same #SymbolicStructures?
		
		b.amalgamated = bounds.clone();

		// the automatic partition splits static / variable relations
		// however, symbolic bounds of static relations may refer to variable relations
		// (even indirectly, for instance, if a var sig extends a static sig)
		// in this automatic splitting they are irrelevant any way, since static are resolved first
		List<Relation> problematic = new LinkedList<Relation>();
		Set<Relation> rs = b.relations_symb; 
		for (Relation r : rs) {
		    if (r.isVariable())
		        problematic.add(r);
		    else 
    			for (Relation d : b.symbolic.deps.get(r))
    				if (d.isVariable())
    					problematic.add(r);
		}
		
		rs.removeAll(problematic);
		
		problematic.clear();
		
		for (Relation r : b.relations)
			if (r.isVariable())
				problematic.add(r);
		
		b.relations.removeAll(problematic);
		
		return b;
	}
	
	/**
	 * Returns the set of all relations bound by this Bounds. The returned set
	 * does not support the add operation. It supports removal iff this is not
	 * an unmodifiable Bounds.
	 * 
	 * @return this.relations
	 */
	public Set<Relation> relations() {
		return relations_all;
	}

	/**
	 * Returns a set view of the relations mapped by the given lower/upper
	 * bounds.
	 * 
	 * @requires lowers.keySet().equals(uppers.keySet())
	 * @return a set view of the relations mapped by the given lower/upper
	 *         bounds
	 */
	// [HASLab] generic types
	private static <T extends Relation> Set<T> relations(final Map<T, ?> lowers1, final Map<T, ?> lowers2, final Map<T, ?> uppers1, final Map<T, ?> uppers2) { 
		return new AbstractSet<T>() {

			public Iterator<T> iterator() {
				return new Iterator<T>() {
					Iterator<T> itr = uppers1.keySet().iterator();
					T last = null;
					boolean second = false;

					public boolean hasNext() {
						if (!second && !itr.hasNext())
							{ itr = uppers2.keySet().iterator(); second = true; }
						return itr.hasNext();
					}

					public T next() {
						if (!second && !itr.hasNext())
							{ itr = uppers2.keySet().iterator(); second = true; }
						return last = itr.next();
					}

					public void remove() {
						itr.remove();
						if (second)
							lowers2.remove(last);
						else 
							lowers1.remove(last);
					}
				};
			}

			public int size() {
				return uppers1.size() + uppers2.size();
			}

			public boolean contains(Object key) {
				return uppers1.containsKey(key) || uppers2.containsKey(key);
			}

			public boolean remove(Object key) {
				return ((uppers1.remove(key) != null) && (lowers1.remove(key) != null)) || 
						((uppers2.remove(key) != null) && (lowers2.remove(key) != null));
			}

			public boolean removeAll(Collection<?> c) {
				return (uppers1.keySet().removeAll(c) && lowers1.keySet().removeAll(c)) ||
						(uppers2.keySet().removeAll(c) && lowers2.keySet().removeAll(c));
			}

			public boolean retainAll(Collection<?> c) {
				return (uppers1.keySet().retainAll(c) && lowers1.keySet().retainAll(c)) || 
						(uppers2.keySet().retainAll(c) && lowers2.keySet().retainAll(c));
			}
		};
	}
	
	/* Temporal bounds */
	
	public boolean hasVarRelations() {
		for (Relation r : relations)
			if (r.isVariable())
				return true;
		for (Relation r : relations_symb)
			if (r.isVariable())
				return true;
		return false;
	}
	
	/* Target-oriented bounds */

	/**
	 * Returns the set of tuples that are the target of r. r may be in
	 * this.relations and not have targets set. If r is not mapped by this, null
	 * is returned.
	 * 
	 * @return r in this.targets.TupleSet => targets[r], null
	 */
	public TupleSet target(Relation r) {
		return targets.get(r);
	}

	/**
	 * Returns a map view of this.targets. The returned map is not modifiable.
	 * 
	 * @return a map view of this.targets
	 */
	public Map<Relation, TupleSet> targets() {
		return unmodifiableMap(targets);
	}

	/**
	 * Returns the weight of r for TO runs. r may be in this.targets and not
	 * have weights set. If r is not mapped by this, null is returned.
	 * 
	 * @return r in this.weights.Int => weights[r], null
	 */
	public Integer weight(Relation r) {
		return weights.get(r);
	}

	/**
	 * Returns a map view of this.weights. The returned map is not modifiable.
	 * 
	 * @return a map view of this.weights
	 */
	public Map<Relation, Integer> weights() {
		return unmodifiableMap(weights);
	}

	/**
	 * Sets the target for the given relation.
	 * 
	 * @requires target in this.upperBound[r] && this.lowerBound[r] in target &&
	 *           target.arity = r.arity && target.universe = this.universe && r
	 *           in this.relations
	 * @ensures this.relations' = this.relations this.lowerBound' =
	 *          this.lowerBound this.upperBound' = this.upperBound this.targets'
	 *          = this.targets ++ r->target this.weights' = this.weights
	 * @throws NullPointerException
	 *             r = null || target = null
	 * @throws IllegalArgumentException
	 *             target.arity != r.arity || upper.universe != this.universe ||
	 *             r !in this.relations || target !in this.upperBound[r] ||
	 *             this.lowerBound[r] !in target
	 */
	public void setTarget(Relation r, TupleSet target) {
		if (!relations().contains(r))
			throw new IllegalArgumentException("r !in this.relations");
		if (!upperBound(r).containsAll(target))
			throw new IllegalArgumentException("target.tuples !in upper.tuples");
		if (!target.containsAll(lowerBound(r)))
			throw new IllegalArgumentException("lower.tuples !in target.tuples");
		targets.put(r, target.clone().unmodifiableView());
	}

	/**
	 * Sets the weight for the given relation.
	 * 
	 * @requires r in this.relations
	 * @ensures this.relations' = this.relations this.lowerBound' =
	 *          this.lowerBound this.upperBound' = this.upperBound this.targets'
	 *          = this.targets this.weights' = this.weights ++ r->weight
	 * @throws NullPointerException
	 *             r = null || weight = null
	 * @throws IllegalArgumentException
	 *             r !in this.relations
	 */
	public void setWeight(Relation r, Integer weight) {
		// TODO: test range of weight
		if (!relations().contains(r))
			throw new IllegalArgumentException("r !in this.relations");
		weights.put(r, weight);
	}

	/* Decomposed bounds */

	public PardinusBounds amalgamated() {
		return amalgamated;
	}

	public boolean integrated() {
		return integrated;
	}
	
	public synchronized PardinusBounds integrated(Solution sol) {
		if (integrated)
			throw new IllegalArgumentException("Already integrated.");
		if (amalgamated == null)
			throw new IllegalArgumentException("Decomposed solving requires decomposed bounds.");
		if (!sol.sat())
			throw new IllegalArgumentException("Can't integrate unsat.");
		
		integration++;
		
		PardinusBounds integrated = amalgamated.clone();

		if (sol.stats().primaryVariables() == 0)
			trivial_config = true;

		for (Relation e : this.relations())
			if (getTupleConfiguration(e.name(), sol.instance()) != null)
				integrated.boundExactly(e,getTupleConfiguration(e.name(), sol.instance()));

		integrated.amalgamated = this.amalgamated;
		integrated.trivial_config = this.trivial_config;
		integrated.integrated = true;
		integrated.integration = this.integration;
		
		return integrated;
	}

	private static TupleSet getTupleConfiguration(String name, Instance s) {
		for (Relation r : s.relationTuples().keySet())
			if (r.name().equals(name))
				return s.relationTuples().get(r);
		return null;
	}

	/* Symbolic bounds */

	/**
	 * Makes the specified expression the upper bound on the contents of the given
	 * relation. The lower bound automatically becomes an NONE expression with
	 * the same arity as the relation.
	 * 
	 * @requires upper.arity = r.arity
	 * @ensures this.relations' = this.relations + r 
	 * 		    this.lowerBound' = this.lowerBound ++ r->NONE^r.arity
	 *          this.upperBound' = this.upperBound ++ r->expr
	 * @throws NullPointerException
	 *             r = null || upper = null
	 * @throws IllegalArgumentException
	 *             upper.arity != r.arity || upper.universe != this.universe
	 */
	public void bound(Relation r, Expression expr) {
		symbolic.checkBound(r, expr);

		Expression none = ConstantExpression.NONE;
		for (int i = 1; i < r.arity(); i++)
			none = none.product(ConstantExpression.NONE);
		
		ComplRelationReplacer rep = new ComplRelationReplacer(symbolic.compls);
		expr = expr.accept(rep);
		
		lowers_symb.put(r, none);
		uppers_symb.put(r, expr);
	}

	/**
	 * Sets both the lower and upper bounds of the given relation to the given
	 * expression.
	 * 
	 * @requires expr.arity = r.arity
	 * @ensures this.relations' = this.relations + r 
	 *          this.lowerBound' = this.lowerBound' ++ r->expr 
	 *          this.upperBound' = this.lowerBound' ++ r->expr
	 * @throws NullPointerException
	 *             r = null || expr = null
	 * @throws IllegalArgumentException
	 *             expr.arity != r.arity || r in *deps(expr)
	 */
	public void boundExactly(Relation r, Expression expr) {
		symbolic.checkBound(r, expr);

		ComplRelationReplacer rep = new ComplRelationReplacer(symbolic.compls);
		expr = expr.accept(rep);
		
		lowers_symb.put(r, expr);
		uppers_symb.put(r, expr);
	}

	/**
	 * Sets the lower and upper bounds for the given relation.
	 * 
	 * @requires lower.arity = upper.arity = r.arity
	 * @ensures this.relations' = this.relations + r
	 *          this.lowerBound' = this.lowerBound ++ r->lower
	 *          this.upperBound' = this.upperBound ++ r->upper
	 * @throws NullPointerException
	 *             r = null || lower = null || upper = null
	 * @throws IllegalArgumentException
	 *             lower.arity != r.arity || upper.arity != r.arity
	 * @throws IllegalArgumentException
	 *             r in *deps(lower) || r in *deps(upper)
	 */
	public void bound(Relation r, Expression lower, Expression upper) {
		symbolic.checkBound(r, lower.union(upper));
		
		ComplRelationReplacer rep = new ComplRelationReplacer(symbolic.compls);
		upper = upper.accept(rep);
		lower = lower.accept(rep);

		lowers_symb.put(r, lower);
		uppers_symb.put(r, upper);
	}

	/**
	 * Returns the relational expression that r must contain (the lower bound on r's
	 * contents). If r is not mapped by this, null is returned.
	 * 
	 * @return r in this.relations => lowerBound[r], null
	 */
	public Expression lowerSymbBound(Relation r) {
		return lowers_symb.get(r);
	}

	/**
	 * Returns the relational expression that r may contain (the upper bound on r's
	 * contents). If r is not mapped by this, null is returned.
	 * 
	 * @return r in this.relations => upperBound[r], null
	 */
	public Expression upperSymbBound(Relation r) {
		return uppers_symb.get(r);
	}

	/**
	 * Returns a map view of this.lowerBound. The returned map is not
	 * modifiable.
	 * 
	 * @return a map view of this.lowerBound
	 */
	public Map<Relation, Expression> lowerSymbBounds() {
		return unmodifiableMap(lowers_symb);
	}

	/**
	 * Returns a map view of this.upperBound. The returned map is not
	 * modifiable.
	 * 
	 * @return a map view of this.upperBound
	 */
	public Map<Relation, Expression> upperSymbBounds() {
		return unmodifiableMap(uppers_symb);	
	}

	private final SymbolicStructures symbolic;
	
	/**
	 * Resolve all symbolic bounds assigned to relations. Will return additional
	 * constraints for non-exact resolutions.
	 * 
	 * @param reporter
	 * @ensures no this.relationSymb 
	 * @return the additional constraints
	 */
	public Formula resolve(Reporter reporter) {
		List<Formula> xtra = new ArrayList<Formula>();
		
		// needed to preserve the order of creation, otherwise non-deterministic results
		List<Relation> rs = new ArrayList<Relation>(relations_symb);
		for (Relation r : rs)
			xtra.addAll(symbolic.resolve(r,reporter));
		Formula res = NaryFormula.and(xtra);
		reporter.debug("Additional resolution formula: "+res);
		return res;
	}

	/**
	 * Tests whether this bounds must be resolved.
	 * @return whether this needs resolving.
	 */
	public boolean resolved() {
		return relations_symb.isEmpty();
	}

	/**
	 * Given a tuple set, returns an expression representing it by composing the
	 * relations that reify each atom, as stored in the <symbolic> structure.
	 * This is needed to specify symbolic bounds that mix both expressions and
	 * particular atoms.
	 * 
	 * @param tset
	 *            the tuple set to be reified.
	 * @return the resulting expression.
	 */
	public Expression reify(TupleSet tset) {
		Expression r = ConstantExpression.NONE;
		for (int i = 1; i < tset.arity(); i++)
			r = r.product(ConstantExpression.NONE);
		
		Iterator<Tuple> it = tset.iterator();
		while (it.hasNext()) {
			Tuple u = it.next();
			Expression r1 = symbolic.reif.get(u.atom(0));
			for (int i = 1; i < u.arity(); i ++)
				r1 = r1.product(symbolic.reif.get(u.atom(i)));
			r = r.union(r1);
		}
		return r;
	}

	/**
	 * Merges the information of another Bounds object into <this>.
	 * Non-mergeable data is overridden.
	 * 
	 * @param bounds
	 *            the bounds to be merged.
	 */
	public void merge(Bounds bounds) {
		if (!(bounds instanceof PardinusBounds))
			for (Relation r : bounds.relations())
				this.bound(r, bounds.lowerBound(r),bounds.upperBound(r));
		else {
			PardinusBounds bnds = (PardinusBounds) bounds;
			for (Relation r : bnds.relations)
				this.bound(r, bnds.lowerBound(r), bnds.upperBound(r));
			for (Relation r : bnds.relations_symb)
				this.bound(r, bnds.lowerSymbBound(r), bnds.upperSymbBound(r));
			for (Relation r : bounds.relations()) {
				if (bnds.target(r) != null)
					this.setTarget(r, bnds.target(r));
				if (bnds.weight(r) != null)
					this.setWeight(r, bnds.weight(r));
			}
			this.symbolic.merge(bnds.symbolic);
			this.integrated = bnds.integrated;
			this.trivial_config = bnds.trivial_config;
		}	
	}

	/**
	 * {@inheritDoc}
	 */
	public PardinusBounds unmodifiableView() {
		return new PardinusBounds(universe().factory(),
				super.lowerBounds(), super.upperBounds(),
				unmodifiableMap(targets), unmodifiableMap(weights),
				unmodifiableMap(lowers_symb), unmodifiableMap(uppers_symb),
				symbolic.unmodifiableView(), unmodifiableSequence(super.intBounds()),
				amalgamated==null?null:amalgamated.unmodifiableView(), integrated, 
				trivial_config,integration);
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public synchronized PardinusBounds clone() {
		try {
				
		    Map<Relation,TupleSet> xx = super.lowerBounds();
		    Map<Relation,TupleSet> yy = super.upperBounds();
			return new PardinusBounds(universe().factory(),
					new LinkedHashMap<Relation, TupleSet>(xx),
					new LinkedHashMap<Relation, TupleSet>(yy),
					new LinkedHashMap<Relation, TupleSet>(targets),
					new LinkedHashMap<Relation, Integer>(weights),
					new LinkedHashMap<Relation, Expression>(lowers_symb),
					new LinkedHashMap<Relation, Expression>(uppers_symb),
					symbolic.clone(),
					super.intBounds().clone(), amalgamated == null?null:amalgamated.clone(),
					integrated, trivial_config, integration);
		} catch (CloneNotSupportedException cnse) {
			throw new InternalError(); // should not be reached
		}
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public String toString() {
		final StringBuilder str = new StringBuilder();
		str.append("constant relation bounds - ");
		for (Map.Entry<Relation, TupleSet> entry : super.lowerBounds()
				.entrySet()) {
			str.append(entry.getKey());
			str.append(": [");
			str.append(entry.getValue());
			TupleSet upper = super.upperBounds().get(entry.getKey());
			if (!upper.equals(entry.getValue())) {
				str.append(", ");
				str.append(upper);
			}
			str.append("] ");
		}
		str.append("\nsymbolic relation bounds - ");
		for (Entry<Relation, Expression> entry : lowers_symb.entrySet()) {
			str.append(entry.getKey());
			str.append(": [");
			str.append(entry.getValue());
			Expression upper = this.upperSymbBounds().get(entry.getKey());
			if (!upper.equals(entry.getValue())) {
				str.append(", ");
				str.append(upper);
			}
			str.append("] ");
		}
		str.append("\nint bounds: ");
		str.append(intBounds());
		if (amalgamated!=null) {
			str.append("\namalgamated:\n\t");
			str.append(amalgamated.toString().replace("\n", "\n\t"));
		}
		return str.toString();
	}
	
	/**
	 * A class that stores information relevant for handling symbolic bounds. This
	 * includes a relation that reifies every atom of the universe into a relation,
	 * the dependencies of these symbolic bounds found thus far, and the
	 * complemented relations needed for correct bound resolution.
	 */
	private class SymbolicStructures {
		private final Map<Object,Relation> reif;
		private final Map<Relation,TupleSet> dereif;
		private final Map<Relation,Set<Relation>> deps;
		private final Map<Relation,Relation> compls;

		/**
		 * Initializes the symbolic structures, by reifying every atom of the
		 * universe.
		 */
		private SymbolicStructures() {
			reif = new HashMap<Object, Relation>();
			dereif = new HashMap<Relation, TupleSet>();
			deps = new HashMap<Relation, Set<Relation>>();
			compls = new HashMap<Relation, Relation>();
			// [HASLab] this will conflict with the reification from the iteration!
			for (int i = 0; i < universe().size(); i++) {
				Relation r = Relation.atom(universe().atom(i).toString());
				reif.put(universe().atom(i), r);
				dereif.put(r, universe().factory().setOf(universe().atom(i)));
			}
		}
		
		/**
		 * Creates a symbolic structure with non-empty information.
		 * 
		 * @param reif
		 *            the relation that reifies each atom.
		 * @param dereif
		 *            the relation that dereifies each relation.
		 * @param deps
		 *            the direct dependencies of symbolically bound relation.
		 * @param compls
		 *            the complemented relations.
		 */
		private SymbolicStructures(Map<Object, Relation> reif,
				Map<Relation, TupleSet> dereif,
				Map<Relation, Set<Relation>> deps,
				Map<Relation, Relation> compls) {
			this.reif = reif;
			this.dereif = dereif;
			this.deps = deps;
			this.compls = compls;
		}

		/**
		 * Checks whether an expression is a valid symbolic bound for a given
		 * relation. Will fail if incorrect arity or cyclic dependency.
		 * 
		 * @param relation
		 *            the relation to be symbolically bound.
		 * @param bound
		 *            the symbolic bound.
		 * @throws IllegalArgumentException bound.arity != r.arity
		 * @throws IllegalArgumentException r in *deps(bounds)
		 */
		private void checkBound(Relation relation, Expression bound) {
			if (relation.arity() != bound.arity())
				throw new IllegalArgumentException("bound.arity != r.arity");
			RelationCollector col = new RelationCollector(new HashSet<Node>());
			Set<Relation> rs = bound.accept(col);
			deps.put(relation, rs);
			rs = transitiveDeps(rs);
			if (rs.contains(relation))
				throw new IllegalArgumentException("r in *deps(bounds)");
		}

		/**
		 * Calculates the reflexive-transitive dependencies of a set of
		 * relations.
		 * 
		 * @param rs
		 *            the relations for which to calculate the dependencies.
		 * @return the transitive dependencies.
		 */
		private Set<Relation> transitiveDeps(Set<Relation> rs) {
			Set<Relation> ds = new HashSet<Relation>(rs);
			
			for (Relation r : rs) {
				Set<Relation> aux = deps.get(r);
				if (aux != null)
					ds.addAll(transitiveDeps(aux));
			}
			
			return ds;
		}

		/**
		 * Resolves a relation's symbolic bounds and all its dependencies. If no
		 * symbolic bounds or already exact constant bounds, does nothing. If bounds are
		 * not exact after resolution, additional constraints are returned, including
		 * all those of dependencies.
		 * 
		 * @param rel      the relation whose bounds are to be resolved.
		 * @param reporter a reporter
		 * @return the extra formulas if the bounds are not exact
		 */
		private List<Formula> resolve(Relation rel, Reporter reporter) {
			List<Formula> constrs = new ArrayList<Formula>();

			if (!relations_symb.contains(rel))
				return constrs;
			
			// resolve all dependencies
			for (Relation dep : deps.get(rel)) {
				List<Formula> tmp = resolve(dep,reporter); 
				constrs.addAll(tmp);
			}
			
			TupleSet pre1 = PardinusBounds.super.lowerBound(rel);
			TupleSet pre2 = PardinusBounds.super.upperBound(rel);
			// if already resolved 
			if (PardinusBounds.super.relations().contains(rel) && pre1.size() == pre2.size()) {
				relations_symb.remove(rel);
				return constrs;
			}
			
			TupleSet low_low = resolveLower(lowerSymbBound(rel));
			TupleSet upp_upp = resolveUpper(upperSymbBound(rel));
			
			if (!upp_upp.containsAll(low_low))
				throw new IllegalArgumentException("Resolved lower larger than resolver upper.");
			
			// resolved symbolic bounds incompatible with known constant bounds
			if (pre1 != null) {
				if (!low_low.containsAll(pre1)) 
					throw new IllegalArgumentException("Resolved lower smaller than constant lower.");
				if (!pre2.containsAll(upp_upp))
					throw new IllegalArgumentException("Resolved upper larger than constant upper.");
			}

			bound(rel, low_low, upp_upp);
			reporter.debug("resolved "+rel+" from ["+pre1+","+pre2+"] into ["+low_low+","+upp_upp+"]");
			
			TupleSet low_upp = resolveUpper(lowerSymbBound(rel));
			TupleSet upp_low = resolveLower(upperSymbBound(rel));

			// resolved bounds not exact, create additional constraints
			Formula constr = null;
			if (low_low.size() != low_upp.size()) {
				if (!lowerSymbBound(rel).equals(Expression.NONE)) {
					Formula x = lowerSymbBound(rel).in(rel);
					constr = constr==null?x:constr.and(x);
				}
			}
			if (upp_low.size() != upp_upp.size()) {
				Formula x = rel.in(upperSymbBound(rel));
				constr = constr==null?x:constr.and(x);
			}
			

			relations_symb.remove(rel);
			
			if (constr != null) {
				// if temporal constraint, quantify universally
				if (TemporalTranslator.isTemporal(constr))
					constr = constr.always();
				constrs.add(constr);
			}
			
			return constrs;
		}
		
		/**
		 * Given the current constant bounds, resolves the lower symbolic bounds of a
		 * relation. Assumes every dependency is already resolved. Relations under
		 * differences are assumed to have been converted into their complement. Must
		 * create eval each time since new bounds are added at each resolution step.
		 * 
		 * @param bound
		 *            the bound to be resolved.
		 * @return the corresponding tuple set.
		 */
		private TupleSet resolveLower(Expression bound) {
			Map<Relation,TupleSet> us = new HashMap<Relation, TupleSet>();
			us.putAll(lowers);
			for (Relation r : symbolic.compls.keySet())
				us.put(compls.get(r), uppers.get(r));
			us.putAll(dereif);
			Instance i = new Instance(universe(), us, intBounds());
			TemporalInstance ti = new TemporalInstance(Arrays.asList(i), 0, 1);
			Evaluator eval = new Evaluator(ti);
			return eval.evaluate(bound,0);
		}

		/**
		 * Given the current constant bounds, resolves the upper symbolic bounds of a
		 * relation. Assumes every dependency is already resolved. Relations under
		 * differences are assumed to have been converted into their complement. Must
		 * create eval each time since new bounds are added at each resolution step.
		 * 
		 * @param bound
		 *            the bound to be resolved.
		 * @return the corresponding tuple set.
		 */
		private TupleSet resolveUpper(Expression e) {
			Map<Relation,TupleSet> us = new HashMap<Relation, TupleSet>();
			us.putAll(uppers);
			for (Relation r : symbolic.compls.keySet())
				us.put(compls.get(r), lowers.get(r));
			us.putAll(dereif);
			Instance i = new Instance(universe(), us, intBounds());
			TemporalInstance ti = new TemporalInstance(Arrays.asList(i), 0, 1);
			Evaluator eval = new Evaluator(ti);
			return eval.evaluate(e,0);
		}

		/**
		 * Merges a symbolic structure into <this>.
		 * 
		 * @param symbolic
		 *            the structure to be merge.
		 */
		public void merge(SymbolicStructures symbolic) {
			reif.putAll(symbolic.reif);
			dereif.putAll(symbolic.dereif);
			deps.putAll(symbolic.deps);
			compls.putAll(symbolic.compls);
		}

		/**
		 * A (deep) clone of this symbolic structure.
		 * 
		 * @return the clone.
		 */
		public SymbolicStructures clone() {
			return new SymbolicStructures(
					new HashMap<Object, Relation>(reif),
					new HashMap<Relation, TupleSet>(dereif),
					new HashMap<Relation, Set<Relation>>(deps),
					new HashMap<Relation, Relation>(compls));
		}

		/**
		 * Returns an unmodifiable view of this symbolic structure.
		 * 
		 * @return the unmodifiable view.
		 */
		public SymbolicStructures unmodifiableView() {
			return new SymbolicStructures(
					unmodifiableMap(reif),
					unmodifiableMap(dereif), 
					unmodifiableMap(deps),
					unmodifiableMap(compls));
		}
	}

}