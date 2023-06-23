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
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import kodkod.ast.ConstantExpression;
import kodkod.ast.Expression;
import kodkod.ast.Relation;
import kodkod.engine.bool.BooleanFactory;
import kodkod.engine.bool.BooleanMatrix;
import kodkod.engine.bool.Dimensions;
import kodkod.engine.config.Options;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;
import kodkod.util.ints.IntIterator;
import kodkod.util.ints.IntRange;
import kodkod.util.ints.IntSet;
import kodkod.util.ints.Ints;
import kodkod.util.ints.SparseSequence;

/** 
 * <p>Interprets the unquantified leaf expressions of a kodkod ast, {@link kodkod.ast.Relation relations} and
 * {@link kodkod.ast.ConstantExpression constant expressions}, as {@link kodkod.engine.bool.BooleanMatrix matrices} of {@link kodkod.engine.bool.BooleanValue
 * boolean values}, and primitive integers as corresponding to particular atoms in the {@link kodkod.instance.Universe universe
 * of discourse}</p>
 * 
 * @specfield universe: Universe
 * @specfield relations: set Relation
 * @specfield ints: set int
 * @specfield lbounds: relations ->one TupleSet 
 * @specfield ubounds: relations ->one TupleSet
 * @specfield ibounds: ints -> one TupleSet
 * @specfield factory: BooleanFactory
 * @specfield vars: relations -> set BooleanVariable
 * @invariant all r: relations | r.arity = lbounds[r].arity = ubounds[r].arity && ubounds[r].containsAll(lbounds[r])
 * @invariant all r: relations | lbounds[r].atoms + ubounds[r].atoms in universe 
 * @invariant all r: relations | #vars[r] = ubounds[r].size() - lbounds[r].size()
 * @invariant all disj r, r': relations | no vars[r] & vars[r']
 * @invariant all i: ints | ibounds[i].arity = ibounds[i].size() = 1
 * @invariant vars[relations] in factory.components
 * 
 * @author Emina Torlak
 */
final class LeafInterpreter {
	private final BooleanFactory factory;
	private final Universe universe;
	private final Map<Relation, IntRange> vars;
	private final Map<Relation, TupleSet> lowers, uppers;
	private final SparseSequence<TupleSet> ints;
	
	/**
	 * Constructs a new LeafInterpreter using the given values.
	 * @requires lowers.keySet() = uppers.keySet()
	 * @ensures this.universe' = universe && this.relations' = lowers.keySet() &&
	 * this.ints' = ints.indices && this.factory' = factory && 
	 * this.ubounds' = uppers && this.lbounds' = lowers && 
	 * this.ibounds' = ints
	 */
	private LeafInterpreter(Universe universe, Map<Relation, TupleSet> lowers, Map<Relation, TupleSet> uppers, 
			SparseSequence<TupleSet> ints, BooleanFactory factory, Map<Relation, IntRange> vars) {
		this.universe = universe;
		this.lowers = lowers;
		this.uppers = uppers;
		this.ints = ints;
		this.factory = factory;
		this.vars = vars;
	}
	
	
	/**
	 * Constructs a new LeafInterpreter using the given values.
	 * @requires lowers.keySet() = uppers.keySet()
	 * @ensures this.universe' = universe && this.relations' = lowers.keySet() &&
	 * this.ints' = ints.indices && this.factory' = factory && 
	 * this.ubounds' = uppers && this.lbounds' = lowers && 
	 * this.ibounds' = ints
	 */
	@SuppressWarnings("unchecked")
	private LeafInterpreter(Universe universe, Map<Relation, TupleSet> rbound, SparseSequence<TupleSet> ints, Options options) {
		this(universe, rbound, rbound, ints, BooleanFactory.constantFactory(options), Collections.EMPTY_MAP);
	}
	
	/**
	 * Returns an overapproximating interpreter for the given bounds and options.
	 * @return some l: LeafInterpreter | l.universe = bounds.universe && l.relations = bounds.relations() && 
	 *           l.ints = bounds.ints() && l.lbounds = l.ubounds = bounds.upperBound && 
	 *           l.ibounds = bounds.intBound && l.factory = BooleanFactory.constantFactory(options) && no l.vars 
	 */
	static final LeafInterpreter overapproximating(Bounds bounds, Options options) {
		return new LeafInterpreter(bounds.universe(), bounds.upperBounds(), bounds.intBounds(), options);
	}
	
	/**
	 * Returns an exact leaf interpreter based on the given instance and options.
	 * @return some l: LeafInterpreter | l.universe = instance.universe && l.relations = instance.relations() && 
	 *           l.ints = instance.ints() && l.lbounds = l.ubounds = instance.relationTuples() && 
	 *           l.ibounds = instance.intTuples && l.factory = BooleanFactory.constantFactory(options) && no l.vars 
	 */
	static final LeafInterpreter exact(Instance instance, Options options) {
		return new LeafInterpreter(instance.universe(), instance.relationTuples(), instance.intTuples(), options);
	}
	
	/**  
	 * Returns an exact interpreter for the given bounds and options. If {@code incremental}  is <code>true</code>, 
	 * then the resulting interpreter can be {@linkplain #extend(Set, Map, Map) extended} with new bindings.  
	 * Otherwise, the interpreter will throw an exception if extension is attempted.
	 * @return some l: LeafInterpreter | l.universe = bounds.universe && l.relations = bounds.relations() && 
	 *          l.ints = bounds.ints() && l.lbounds = bounds.lowerBound && l.ubounds = bounds.upperBound && 
	 *          l.ibounds = bounds.intBound && 
	 *          l.factory = BooleanFactory.factory(sum(r: l.relations | #(l.ubounds[r]-l.lbounds[r]))-1, options) &&
	 *          l.vars[relations] = l.factory & BooleanVariable
	 */
	static final LeafInterpreter exact(Bounds bounds, Options options, boolean incremental) {
		final Map<Relation, IntRange> vars = new LinkedHashMap<Relation,IntRange>();
		final Map<Relation, TupleSet> lowers = incremental ? new LinkedHashMap<Relation, TupleSet>(bounds.lowerBounds()) : bounds.lowerBounds();
		final Map<Relation, TupleSet> uppers = incremental ? new LinkedHashMap<Relation, TupleSet>(bounds.upperBounds()) : bounds.upperBounds();
		final int numVars = allocateVars(1, vars, bounds.relations(), lowers, uppers);
		return new LeafInterpreter(bounds.universe(), lowers, uppers, bounds.intBounds(), BooleanFactory.factory(numVars, options), vars);
	}
	
	/**
	 * Returns an empty interpreter which cannot be {@linkplain #extend(Set, Map, Map) extended} with new mappings.
	 * @return some l: LeafInterpreter | l.universe = universe && no l.relations  && 
	 *           no l.ints && l.factory = BooleanFactory.constantFactory(options)  
	 */
	@SuppressWarnings("unchecked")
	static final LeafInterpreter empty(Universe universe, Options options) {
		return new LeafInterpreter(universe, (Map<Relation, TupleSet>)Collections.EMPTY_MAP, 
				(SparseSequence<TupleSet>)Ints.EMPTY_SEQUENCE, options);
	}
	
	/**
	 * Populates the {@code vars} map with bindings from each relation in {@code rels} to an integer range,
	 * which specifies the identifiers of the variables used to encode the contents of that relation.  The 
	 * resulting integer ranges put together form a complete range that starts at {@code minVar}.
	 * @requires lowers.universe = uppers.universe 
	 * @requires all r: rels | lowers.get(r).tuples in uppers.get(r).tuples 
	 * @ensures vars.map' = vars.map ++ 
	 *          { r: rels, v: IntRange | v.size() = uppers.get(r).size() - lowers.get(r).size() && v.size() > 0 }
	 * @ensures min(vars.map'[rels]) = minVar && max(vars.map'[rels]) = minVar + (sum r: rels | vars.map'[r].size()) - 1
	 * @return sum r: rels | vars.map'[r].size()
	 */
	private static int allocateVars(int minVar, Map<Relation, IntRange> vars, Set<Relation> rels, Map<Relation, TupleSet> lowers, Map<Relation, TupleSet> uppers) {
		int maxLit = minVar;
		for(Relation r : rels) {
			int rLits = uppers.get(r).size() - lowers.get(r).size();
			if (rLits > 0) {
				vars.put(r, Ints.range(maxLit, maxLit + rLits - 1));
				maxLit += rLits;
			}
		}
		return maxLit - minVar;
	}
	
	/**
	 * Returns this.factory.
	 * @return this.factory.
	 */
	public final BooleanFactory factory() {
		return this.factory;
	}
	
	/**
	 * Returns the universe of discourse.
	 * @return this.universe
	 */
	public final Universe universe() {
		return universe;
	}
	
	/**
	 * Returns this.vars.
	 * @return this.vars.
	 */
	public final Map<Relation, IntSet> vars() {
		final Map<Relation, IntSet> ret = new LinkedHashMap<Relation,IntSet>((vars.size() * 4)/3);
		for(Map.Entry<Relation, IntRange> e: vars.entrySet()) {
			ret.put(e.getKey(), Ints.rangeSet(e.getValue()));
		}
		return ret;
	}
	
	/**
	 * Returns a set view of the variables assigned to the given relation, or empty set 
	 * if no variables were assigned to the given relation.
	 * @return this.vars[r]
	 */
	public final IntSet vars(Relation r) { 
		final IntRange v = vars.get(r);
		return v==null ? Ints.EMPTY_SET : Ints.rangeSet(v); 
	}
	
	/**
	 * Extends this interpreter with interpretations for the given relations, based on 
	 * the specified lower and upper bound on each relation's value.  Note that this 
	 * method may fail if the underlying boolean factory does not permit introduction 
	 * of new variables.
	 * @requires no rels & this.relations
	 * @requires rels in lowers.keySet() && rels in uppers.keySet()
	 * @requires all r: rels | let lr = lowers.get(r), ur = uppers.get(r) |
	 *            lr.tuples in ur.tuples && lr.universe = ur.universe = this.universe
	 * @ensures this.relations' = this.relations +  rels && 
	 *          this.lbounds' = this.lbounds + rels<:(lowers.map) && 
	 *          this.ubounds' = this.ubounds + rels<:(uppers.map) &&
	 *          let newVars = this.factory.components' - this.factory.components | 
	 *          	  newVars in BooleanVariable && 
	 *                #newVars = (sum r: rels | uppers.get(r).size() - lowers.get(r).size()) &&
	 *                (this.vars' - this.vars) in rels -> newVars
	 * @return this
	 */
	public final void extend(Set<Relation> rels, Map<Relation, TupleSet> lowers, Map<Relation, TupleSet> uppers) { 	
		for(Relation r : rels) {
			this.lowers.put(r, lowers.get(r));
			this.uppers.put(r, uppers.get(r));
		}
		factory.addVariables(allocateVars(factory.maxFormula()+1, vars, rels, lowers, uppers));
	}
	
	/**
	 * Returns a {@link kodkod.engine.bool.BooleanMatrix matrix} m of 
	 * {@link kodkod.engine.bool.BooleanValue boolean formulas} representing
	 * the specified relation.    
	 * @requires r in this.relations
	 * @return { m: BooleanMatrix | let lset = (this.rBounds[r].TupleSet).tuples.index, 
	 *           hset = (this.rBounds[r][TupleSet]).tuples.index, dset = [0..this.universe.size()^r.arity) | 
	 *           m.dimensions.dimensions = [0..r.arity) ->one this.universe.size() && 
	 *           m.elements[lset] = TRUE && m.elements[dset-hset] = FALSE &&
	 *           all disj i, j: hset-lset | m.elements[i]+m.elements[j] in this.vars[r] && 
	 *            m.elements[i].label < m.elements[j].label <=> i < j }
	 * @throws UnboundLeafException  r !in this.relations
	 */
	public final BooleanMatrix interpret(Relation r) {
		if (!lowers.containsKey(r))
			throw new UnboundLeafException("Unbound relation: ", r);
		final IntSet lowerBound = lowers.get(r).indexView();
		final IntSet upperBound = uppers.get(r).indexView();
		
		final BooleanMatrix m = factory.matrix(Dimensions.square(universe().size(), r.arity()), upperBound, lowerBound);
		
		if (upperBound.size() > lowerBound.size()) {
			int varId = vars.get(r).min();
			for (IntIterator indeces = upperBound.iterator(); indeces.hasNext();) {
				int tupleIndex = indeces.next();
				if (!lowerBound.contains(tupleIndex))  
					m.set(tupleIndex, factory.variable(varId++));
			}
		}
		return m;
	}
	
	/**
	 * Returns a {@link kodkod.engine.bool.BooleanMatrix matrix} m of 
	 * {@link kodkod.engine.bool.BooleanValue boolean formulas} representing
	 * the specified constant expression.    
	 * @return { m: BooleanMatrix | let dset = [0..this.universe.size()^c.arity) | 
	 *           m.dimensions.dimensions = [0..c.arity) ->one this.universe.size() && 
	 *           c = UNIV => m.elements[dset] = TRUE, c = NONE => m.elements[dset] = FALSE,
	 *           c = IDEN => (all i: dset | (some j: int | i = j*(1+this.universe.size())) => m.elements[i] = TRUE, m.elements[i] = FALSE),
	 *           c = INT => (all i: dset | (some j: int | this.interpret(j)=i) => m.elements[i] = TRUE, m.elements[i] = FALSE }
	 */
	public final BooleanMatrix interpret(ConstantExpression c) {
		final int univSize = universe().size();
		if (c==Expression.UNIV) {
			final IntSet all =  Ints.rangeSet(Ints.range(0, univSize-1));
			return factory().matrix(Dimensions.square(univSize, 1), all, all);
		} else if (c==Expression.IDEN) {
			final Dimensions dim2 = Dimensions.square(univSize, 2);
			final IntSet iden = Ints.bestSet(dim2.capacity());
			for(int i = 0; i < univSize; i++) {
				iden.add(i*univSize + i);
			}			
			return factory().matrix(dim2, iden, iden);
		} else if (c==Expression.NONE) {
			return factory().matrix(Dimensions.square(univSize, 1), Ints.EMPTY_SET, Ints.EMPTY_SET);
		} else if (c==Expression.INTS) {
			final IntSet ints = Ints.bestSet(univSize);
			for(IntIterator iter = ints().iterator(); iter.hasNext(); ) {
				ints.add(interpret(iter.next()));
			}
			return factory().matrix(Dimensions.square(univSize, 1), ints, ints);
		} else {
			throw new IllegalArgumentException("unknown constant expression: " + c);
		}
	}
	
	/**
	 * Returns the set of all integers corresponding to some
	 * atom in this.universe.
	 * @return this.ints
	 */
	public final IntSet ints() {
		return ints.indices();
	}
	
	/**
	 * Returns the index of the atom from this.universe which represents the given integer.
	 * @requires i in this.ints
	 * @return this.ibounds[i].indexView().min()               
	 */
	public final int interpret(int i) {
		return ints.get(i).indexView().min();
	}
}
