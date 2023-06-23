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

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import kodkod.ast.Decls;
import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.IntConstant;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.Evaluator;
import kodkod.engine.decomp.DecompFormulaSlicer;
import kodkod.engine.ltl2fol.TemporalBoundsExpander;
import kodkod.engine.ltl2fol.TemporalTranslator;
import kodkod.util.ints.IndexedEntry;

/**
 * Represents a temporal instance of a temporal relational problem containing
 * {@link kodkod.ast.VarRelation variable relations} in the
 * {@link kodkod.instance.TemporalBounds temporal bounds}.
 * 
 * As of Pardinus 1.2, a looping state is always assumed to exist (i.e., they
 * always represent an infinite path).
 * 
 * A temporal instance has two interpretations. One is essentially a set of
 * states and a looping state, the other a static {@link Instance} under a state
 * idiom, so that the Kodkod {@link Evaluator} can be used.
 * 
 * @author Nuno Macedo // [HASLab] temporal model finding
 */
public class TemporalInstance extends Instance {

	/** The states comprising the trace. */
	private final List<Instance> states;
	/** The looping state. */
	public final int loop;
	/** The looping state. */
	public final int unrolls;
	private final Universe static_universe;

	/**
	 * Creates a new temporal instance from a sequence of states and a looping
	 * state. Will make <code>this</code> a matching static instance so that the
	 * {@link Evaluator} can be used, with an extended universe.
	 * 
	 * As of Pardinus 1.2, loops are assumed to always exist.
	 * 
	 * @assumes 0 >= loop >= instances.length
	 * @assumes all s,s': instance | s.universe = s'.universe && s.intTuples =
	 *          s'.intTuples
	 * @param instances the states of the temporal instance.
	 * @param loop      the looping state.
	 * @ensures this.states = instances && this.loop = loop
	 * @throws NullPointerException     instances = null
	 * @throws IllegalArgumentException !(0 >= loop >= instances.length)
	 */
	public TemporalInstance(List<Instance> instances, int loop, int unrolls) {
		super(TemporalBoundsExpander.expandUniverse(instances.get(0).universe(), instances.size(), unrolls));
		if (loop < 0 || loop >= instances.size())
			throw new IllegalArgumentException("Looping state must be between 0 and instances.length.");

		Map<Relation, TupleSet> expRels = stateIdomify(this.universe(), instances, loop, unrolls);
		for (Relation r : expRels.keySet())
			super.add(r, expRels.get(r));
		for (IndexedEntry<TupleSet> entry : instances.get(0).intTuples())
			super.add(entry.index(), universe().factory().setOf(entry.value().iterator().next().atom(0)));

		this.static_universe = instances.get(0).universe();
		this.states = instances;
		this.loop = loop;
		this.unrolls = unrolls;
	}

	/**
	 * Converts a sequence of instances into a state idiom representation by
	 * appending the corresponding state atom to variable relations.
	 * 
	 * @param instances the sequence of instances representing a trace
	 * @return the trace represented in a state idiom
	 */
	private static Map<Relation, TupleSet> stateIdomify(Universe u, List<Instance> instances, int loop, int unrolls) {
		assert (loop >= 0 && loop < instances.size());
		// first instances.size() atoms will be the state atoms
		Map<Relation, TupleSet> instance = new HashMap<Relation, TupleSet>();
		for (Relation r : instances.get(0).relations())
			if (r.isVariable()) {
				if (instance.get(r.getExpansion()) == null)
					instance.put(r.getExpansion(), u.factory().noneOf(r.arity() + 1));
				for (int i = 0; i < instances.size(); i++) {
					TupleSet ts = TemporalBoundsExpander.convertToUniv(instances.get(i).tuples(r), u);
					instance.get(r.getExpansion()).addAll(ts.product(u.factory().setOf(u.atom(i))));
				}
			} else {
				TupleSet ts = u.factory().noneOf(r.arity());
				for (Tuple t : instances.get(0).tuples(r)) {
					List<Object> lt = new ArrayList<Object>();
					for (int j = 0; j < t.arity(); j++)
						lt.add(t.atom(j));
					ts.add(u.factory().tuple(lt));
				}
				instance.put(r, ts);
			}
		instance.put(TemporalTranslator.LAST, u.factory().setOf(u.atom(instances.size() * unrolls - 1)));
		instance.put(TemporalTranslator.FIRST, u.factory().setOf(u.atom(0)));
		instance.put(TemporalTranslator.LOOP, u.factory().setOf(u.atom(instances.size() * (unrolls - 1) + loop)));
		TupleSet x = u.factory().range(u.factory().tuple(u.atom(0)), u.factory().tuple(u.atom(instances.size() - 1)));
		for (int i = 1; i < unrolls; i++) {
			x.addAll(u.factory().range(u.factory().tuple(u.atom(i * instances.size() + loop)),
					u.factory().tuple(u.atom((i + 1) * instances.size() - 1))));
		}
		instance.put(TemporalTranslator.STATE, x);
		if (unrolls > 1) { // otherwise no need for unrolls
			TupleSet unrollMap = u.factory().noneOf(2);
			for (int i = 0; i < instances.size(); i++) {
				for (int j = 0; j < unrolls; j++)
					unrollMap.add(u.factory().tuple(u.atom(i + j * instances.size()), u.atom(i)));
			}
			instance.put(TemporalTranslator.UNROLL_MAP, unrollMap);
			instance.put(TemporalTranslator.LAST_, u.factory().setOf(u.atom(instances.size() - 1)));
		}

		TupleSet nxt = u.factory().noneOf(2);
		for (int i = 0; i < instances.size() - 1; i++)
			nxt.add(u.factory().tuple(u.atom(i), u.atom(i + 1)));
		for (int j = 1; j < unrolls; j++) {
			nxt.add(u.factory().tuple(u.atom(j * instances.size() - 1), u.atom(j * instances.size() + loop)));
			for (int i = loop; i < instances.size() - 1; i++)
				nxt.add(u.factory().tuple(u.atom(j * instances.size() + i), u.atom(j * instances.size() + i + 1)));
		}
		instance.put(TemporalTranslator.PREFIX, nxt);
		return instance;
	}

	/**
	 * Creates a new temporal instance from a static instance in the state idiom.
	 * The shape of the trace are retrieved from the evaluation of the
	 * {@link kodkod.engine.ltl2fol.TemporalTranslator#STATE time} relations. The
	 * original variable relations (prior to expansion) are also considered since
	 * they contain information regarding their temporal properties.
	 * 
	 * @assumes some instance.loop
	 * @param instance the expanded static solution to the problem
	 * @param tmptrans temporal translation information, including original variable
	 *                 relations
	 * @throws IllegalArgumentException no instance.loop
	 */
	public TemporalInstance(Instance instance, PardinusBounds extbounds) {
		super(instance.universe(), new HashMap<Relation, TupleSet>(instance.relationTuples()), instance.intTuples());
		Evaluator eval = new Evaluator(this);
		// evaluate last relation
		Tuple tuple_last = eval.evaluate(TemporalTranslator.LAST).iterator().next();
		int end = TemporalTranslator.interpretState(tuple_last);
		// evaluate loop relation
		TupleSet tupleset_loop = eval.evaluate(TemporalTranslator.LOOP);
		if (!tupleset_loop.iterator().hasNext())
			throw new IllegalArgumentException("Looping state must exist.");
		Tuple tuple_loop = tupleset_loop.iterator().next();
		loop = TemporalTranslator.interpretState(tuple_loop);
		unrolls = TemporalTranslator.interpretUnroll(tuple_loop);
		states = new ArrayList<Instance>();

		Iterator<Tuple> tupleset_times = eval.evaluate(TemporalTranslator.STATE).iterator();
		Set<Object> atom_times = new HashSet<Object>();
		while (tupleset_times.hasNext())
			atom_times.add(tupleset_times.next().atom(0));

		List<Object> atoms = new ArrayList<Object>();
		Iterator<Object> old_atoms = extbounds.universe().iterator();
		while (old_atoms.hasNext())
			atoms.add(old_atoms.next());

		static_universe = new Universe(atoms);
		// for each state, create a new instance by evaluating relations at that state
		for (int i = 0; i <= end; i++) {
			Instance inst = new Instance(static_universe);

			for (Relation r : extbounds.relations()) {
				TupleSet ts = static_universe.factory().noneOf(r.arity());
				for (Tuple t : eval.evaluate(r, i)) {
					List<Object> lt = new ArrayList<Object>();
					for (int j = 0; j < t.arity(); j++)
						lt.add(t.atom(j));
					ts.add(static_universe.factory().tuple(lt));
				}
				inst.add(r, ts);
			}

			for (IndexedEntry<TupleSet> entry : extbounds.intBounds()) {
				Tuple t = static_universe.factory().tuple(entry.value().iterator().next().atom(0));
				inst.add(entry.index(), static_universe.factory().setOf(t));
			}

			states.add(inst);
		}
	}

	/**
	 * Converts a temporal instance into a formula that exactly identifies it,
	 * encoding each state of the trace and the looping behavior. Requires that
	 * every relevant atom be reified into a singleton relation, which may be
	 * re-used between calls. Will be used between the various states of the trace.
	 * 
	 * Not all relations are converted into the resulting formula, <formula> is used
	 * to identify which are relevant.
	 * 
	 * Will change <bounds> if not all atoms of the universe are present at <reif>.
	 * 
	 * @assumes reif != null
	 * @param reif    the previously reified atoms
	 * @param formula formula used to identify the relevant relations
	 * @param bounds  the declaration of the relations
	 * @throws NullPointerException reif = null
	 * @return the formula representing <this>
	 */
	// [HASLab]
	@Override
	public Formula formulate(Map<Object, Expression> reif, Formula formula, boolean someDisj, Bounds bounds) {
		return formulate(bounds, reif, formula, -1, null, someDisj, true);
	}

	@Override
	public Formula formulate(Map<Object, Expression> reif, Formula formula, boolean someDisj, Bounds bounds, boolean localUniv) {
		return formulate(bounds, reif, formula, -1, null, someDisj, localUniv);
	}

	public Formula formulate(Bounds bounds, Map<Object, Expression> reif, Formula formula, int start, Integer end, boolean someDisj) {
		return formulate(bounds, reif, formula, start, end, someDisj, true);
	}

	/**
	 * Converts a segment of a temporal instance into a formula that exactly
	 * identifies it, encoding each state of the trace and the looping behavior.
	 * Requires that every relevant atom be reified into a singleton relation, which
	 * may be re-used between calls. Will be used between the various states of the
	 * trace.
	 * 
	 * If the end is left null, it represents the complete looping suffix; the start
	 * can be -1 to denote only the static portion of the trace.
	 * 
	 * Not all relations are converted into the resulting formula, <formula> is used
	 * to identify which are relevant.
	 * 
	 * Will change <bounds> if not all atoms of the universe are present at <reif>.
	 * 
	 * NOTE: the <bounds> representing the instance contain a universe that is not
	 * the one of the original problem; thus, local universe restrictions will only
	 * consider those atoms.
	 * 
	 * @assumes reif != null
	 * @assumes start >= -1
	 * @assumes end >= start or end == null
	 * @param bounds  the declaration of the relations
	 * @param reif    the previously reified atoms
	 * @param formula formula used to identify the relevant relations
	 * @param start   the beginning of the segment
	 * @param end     the end of the segment (or null if infinite)
	 * @throws NullPointerException reif = null
	 * @return the formula representing <this>
	 */
	// [HASLab]
	public Formula formulate(Bounds bounds, Map<Object, Expression> reif, Formula formula, int start, Integer end, boolean someDisj, boolean localUniv) {
		if (start < -1)
			throw new IllegalArgumentException("Segment start must be >= -1.");
		if (end != null && end < start)
			throw new IllegalArgumentException("Segment end must be after its start (or null if infinite).");

		// reify atoms not yet reified
		Universe sta_uni = states.get(0).universe();
		for (int i = 0; i < sta_uni.size(); i++) {
			// integers do not need to be quantified
			if (!sta_uni.atom(i).toString().matches("-?\\d+")) {
				Expression r;
				if (!reif.keySet().contains(sta_uni.atom(i))) { 
					if (someDisj) {
						r = Variable.unary(sta_uni.atom(i).toString());
					} else {
						r = Relation.atom(sta_uni.atom(i).toString());
					}
					reif.put(sta_uni.atom(i), r);
				} else {
					r = reif.get(sta_uni.atom(i));
				}
				if (!someDisj && !bounds.relations.contains(r))
					bounds.boundExactly((Relation) r, bounds.universe().factory().setOf(sta_uni.atom(i)));
			}
		}

		Set<Relation> staticss = new HashSet<Relation>();
		for (Relation r : states.get(0).relations())
			if (!r.isVariable())
				staticss.add(r);
		// split between static and variable formula for relevancy formula
		Entry<Formula, Formula> slcs = DecompFormulaSlicer.slice(formula, staticss);

		// create the constraint for each state within the given segment
		// (S0 and after (S1 and after ...)) and (loop formula)
		Formula res;
		if (states.isEmpty())
			res = Formula.TRUE;
		else {
			Integer j = end;
			// if null then end at the last state of the prefix, unless the start is beyond
			// it
			// TODO: the looping formula should also be offset in this case!
			if (j == null)
				j = Integer.max(start + (prefixLength() - 1) - loop, prefixLength() - 1);
			if (j != null && j >= 0) {
				// the state formulas, start from the end and accumulate afters
				res = state(j--).formulate(reif, slcs.getValue(), someDisj, bounds, !localUniv);
				for (; j >= Integer.max(0, start); j--)
					res = state(j).formulate(reif, slcs.getValue(), someDisj, bounds, !localUniv).and(res.after());
				// after offset when start > 0
				for (; j >= 0; j--)
					res = res.after();
			} else
				res = Formula.TRUE;

			// the configuration formula, if start = -1
			if (start < 0 && !slcs.getKey().equals(Formula.TRUE)) {
				Formula sres = states.get(prefixLength() - 1).formulate(reif, slcs.getKey(), someDisj, bounds, false);
				res = res.equals(Formula.TRUE) ? sres : sres.and(res);
			}

			// only create null formula if no end to segment, end = nukk
			if (end == null) {
				// create the looping constraint
				// after^loop always (Sloop => after^(end-loop) Sloop && Sloop+1 =>
				// after^(end-loop) Sloop+1 && ...)
				Formula rei = states.get(loop).formulate(reif, slcs.getValue(), someDisj, bounds, !localUniv);
				Formula rei2 = rei;
				for (int i = loop; i < prefixLength(); i++)
					rei2 = rei2.after();

				Formula looping = rei.implies(rei2);
				for (int i = loop + 1; i < prefixLength(); i++) {
					rei = states.get(i).formulate(reif, slcs.getValue(), someDisj, bounds, !localUniv);
					rei2 = rei;
					for (int k = loop; k < prefixLength(); k++)
						rei2 = rei2.after();
					looping = looping.and(rei.implies(rei2));
				}
				looping = looping.always();
				for (int i = 0; i < loop; i++)
					looping = looping.after();

				res = res.and(looping);
			}

			if (someDisj) {
				Decls decls = null;
				Expression al = null;
				for (Expression e : reif.values()) {
					if (decls == null) {
						al = e;
						decls = ((Variable) e).oneOf(Expression.UNIV);
					} else {
						al = al.union(e);
						decls = decls.and(((Variable) e).oneOf(Expression.UNIV));
					}
				}
				for (int i = 0; i < sta_uni.size(); i++)
					if (sta_uni.atom(i).toString().matches("-?\\d+"))
						al = al.union(IntConstant.constant(Integer.valueOf(sta_uni.atom(i).toString())).toExpression());
				if (localUniv)
					res = (al.eq(Expression.UNIV)).and(res);
				res = res.forSome(decls);
			}
		}

		return res;
	}

	/**
	 * {@inheritDoc}
	 */
	public boolean contains(Relation relation) {
		return super.contains(relation) || (states != null && !states.isEmpty() && states.get(0).contains(relation));
	}

	/**
	 * Creates the set of isomorphic instances with n extra states. Calculates all
	 * possible loop unfoldings.
	 * 
	 * @param size       the size of the unrolled instances
	 * @param past_depth the past depth, needed to preserve the size of the universe
	 */
	public Set<TemporalInstance> unrollStep(int size, int past_depth) {
		// the number of needed extra steps
		Set<TemporalInstance> instances = new HashSet<TemporalInstance>();
		// always initialize with the prefix
		ArrayList<Instance> newstates = new ArrayList<Instance>();
		for (int i = 0; i < Math.min(size, prefixLength()); i++)
			newstates.add(this.states.get(i));
		size -= prefixLength();
		int loopsize = prefixLength() - loop;
		// add the corresponding unrolled states
		for (int i = 0; i < size; i++)
			newstates.add(this.states.get((i % loopsize) + loop));

		// creates a new instance for every isomorphic loop (multiples of loop size
		// after the prefix)
		int newloop = loop + size;
		while (newloop >= loop) {
			instances.add(new TemporalInstance(newstates, newloop, past_depth));
			newloop -= loopsize;
		}
		// sometimes there is the need to trim down the instance to smaller prefixes so
		// that the appropriate vars are created; however, a loop is also required when
		// creating a trace, so 0 is a default, it does not represent the actual
		// instance
		if (size < 0)
			instances.add(new TemporalInstance(newstates, 0, past_depth));

		return instances;
	}

	/**
	 * The length of the prefix of this temporal instance, i.e., the number of
	 * unique states prior to looping.
	 * 
	 * @return
	 */
	public int prefixLength() {
		return states.size();
	}

	/**
	 * Retrieves the i-th state of this trace, considering the normalization of
	 * indices after looping.
	 * 
	 * @param i
	 * @return
	 */
	public Instance state(int i) {
		return states.get(normalizedIndex(i));
	}

	/**
	 * Calculates the normalized index for this instance considering the looping
	 * states.
	 * 
	 * @param i
	 * @return
	 */
	public int normalizedIndex(int i) {
		int loopsize = prefixLength() - loop;
		return i < prefixLength() ? i : (((i - prefixLength()) % loopsize) + loop);
	}

	/**
	 * Returns the static universe from which the tuples in the temporal instance
	 * are drawn. Contrasts with {@link #universe()} that represents the expanded
	 * version of the instance.
	 * 
	 * @return this.static_universe
	 */
	public Universe staticUniverse() {
		return static_universe;
	}

	/**
	 * Maps the given relation to the given tuple set.
	 * 
	 * @ensures this.tuples' = this.tuples ++ relation->s
	 * @throws NullPointerException          relation = null || s = null
	 * @throws IllegalArgumentException      relation.arity != s.arity
	 * @throws IllegalArgumentException      s.universe != this.universe
	 * @throws UnsupportedOperationException this is an unmodifiable instance
	 */
	public void add(final Relation relation, TupleSet s) {
		if (!s.universe().equals(universe()) && !s.universe().equals(staticUniverse()))
			throw new IllegalArgumentException("s.universe!=this.universe");
		if (relation.arity() != s.arity())
			throw new IllegalArgumentException("relation.arity!=s.arity");

		if (s.universe().equals(universe())) {
			super.add(relation, s);
			for (int i = 0; i < states.size(); i++) {
				states.get(i).add(relation, TemporalBoundsExpander.convertToUniv(s, static_universe));
			}
		} else {
			super.add(relation, TemporalBoundsExpander.convertToUniv(s, universe()));
			for (int i = 0; i < states.size(); i++) {
				states.get(i).add(relation, s);
			}
		}
	}

	/**
	 * {@inheritDoc}
	 * 
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		for (int i = 0; i < prefixLength(); i++) {
			sb.append("* state " + i);
			if (loop == i)
				sb.append(" LOOP");
			if (prefixLength() - 1 == i)
				sb.append(" LAST");
			sb.append("\n" + states.get(i).toString());
			sb.append("\n");
		}
		return sb.toString();
	}

	/**
	 * Returns an unmodifiable view of this instance.
	 * 
	 * @return an unmodifiable view of this instance.
	 */
	public TemporalInstance unmodifiableView() {
		return new TemporalInstance(Collections.unmodifiableList(states), loop, unrolls);
	}
}
