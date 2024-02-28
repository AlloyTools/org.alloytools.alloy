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
package kodkod.engine.ltl2fol;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import kodkod.ast.Relation;
import kodkod.engine.Evaluator;
import kodkod.instance.Bounds;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TemporalInstance;
import kodkod.instance.Tuple;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;
import kodkod.util.ints.IndexedEntry;

/**
 * An extension to the regular Kodkod {@link Bounds bounds} that stores
 * information regarding its origin from bounds over {@link VarRelation variable
 * relations}. Translates {@link VarRelation variable relation} bounds into its
 * standard representation, by creating a new extended universe, appending the
 * {@link TemporalTranslator#STATE state} atoms to the bounds. The bounds of
 * static relations should remain unchanged.
 * 
 * Two alternative encodings depending on the {@link TemporalTranslator#ExplicitUnrolls
 * strategy} to support past-time operators.
 * 
 * As of Pardinus 1.1, traces are assumed to always loop.
 *
 * @author Eduardo Pessoa, Nuno Macedo // [HASLab] temporal model finding
 */
public class TemporalBoundsExpander {

	/**
	 * Expands the old bounds by converting the bounds over variable relations into
	 * regular bounds with {@link TemporalTranslator#STATE state} atoms appended. It
	 * also creates and binds the relations representing the trace.
	 * 
	 * Currently assumes that traces are always infinite.
	 * 
	 * @assumes unrolls > 0
	 * @assumes states > 0
	 * @assumes bounds.resolved()
	 * @param bounds
	 *            the bounds with variable relations to be expanded.
	 * @param steps
	 *            the number of distinguished states in the trace.
	 * @param unrolls
	 *            the number of trace unrolls.
	 * @return the expanded bounds.
	 * @throws IllegalArgumentException
	 *             unrolls < 1 || states < 1 || !bounds.resolved().
	 * @throws UnsupportedOperationException
	 *             if loops are not forced.
	 */
	public static PardinusBounds expand(PardinusBounds bounds, int steps, int unrolls) {
		if (unrolls < 1 || steps < 1)
			throw new IllegalArgumentException("Number of unrolls or steps <1.");
		if (!bounds.resolved())
			throw new IllegalArgumentException("Symbolic bounds must be resolved at this stage.");
		Universe u = expandUniverse(bounds.universe(), steps, unrolls);
		return expand(bounds, u, steps, unrolls);
	}

	/**
	 * Actually expands temporal bounds into their static representation as regular
	 * bounds with {@link TemporalTranslator#STATE state} atoms appended, unrolled a
	 * certain number of times.
	 * 
	 * Bounds are assumed to already be resolved at this point. If the loop is known
	 * to necessarily loop, simplifications will be applied.
	 * 
	 * Two alternative encodings depending on the {@link TemporalTranslator#ExplicitUnrolls
	 * strategy} to support past-time operators.
	 * 
	 * @param bounds
	 *            the bounds with variable relations to be expanded.
	 * @param uni
	 *            the new universe with state atoms.
	 * @param steps
	 *            the number of distinguished states in the trace.
	 * @param unrolls
	 *            the number of trace unrolls.
	 * @param force_loop
	 *            whether the trace will necessarily loop.
	 * @return the expanded bounds with the new universe.
	 */
	private static PardinusBounds expand(PardinusBounds bounds, Universe uni, int steps, int unrolls) {
		assert(unrolls > 0);
		assert(steps > 0);
		assert(bounds.resolved());

		PardinusBounds newBounds = new PardinusBounds(uni);

		TupleSet tupleSetTime_unr_first;

		if (TemporalTranslator.ExplicitUnrolls) {

			String sp = TemporalTranslator.STATE_SEP;
			newBounds.boundExactly(TemporalTranslator.FIRST,uni.factory().setOf(uni.factory().tuple(TemporalTranslator.STATEATOM + "0" + sp + "0")));
			newBounds.boundExactly(TemporalTranslator.LAST, uni.factory().setOf(uni.factory().tuple(TemporalTranslator.STATEATOM + (steps - 1) + sp + (unrolls - 1))));
			newBounds.boundExactly(TemporalTranslator.LAST_,uni.factory().setOf(uni.factory().tuple(TemporalTranslator.STATEATOM + (steps - 1) + sp + 0)));

			TupleSet tupleSetTime_unr = uni.factory().range(
					uni.factory().tuple(TemporalTranslator.STATEATOM + "0" + sp + "0"),
					uni.factory().tuple(TemporalTranslator.STATEATOM + (steps - 1) + sp + (unrolls - 1)));
			tupleSetTime_unr_first = uni.factory().range(
					uni.factory().tuple(TemporalTranslator.STATEATOM + "0" + sp + "0"),
					uni.factory().tuple(TemporalTranslator.STATEATOM + (steps - 1) + sp + "0"));
			TupleSet tupleSetTime_unr_first_lasts = uni.factory().setOf(tupleSetTime_unr_first);
			for (int j = 0; j < unrolls; j++)
				tupleSetTime_unr_first_lasts.add(uni.factory().tuple(TemporalTranslator.STATEATOM + (steps - 1) + sp + j));
			newBounds.bound(TemporalTranslator.STATE, tupleSetTime_unr_first_lasts, tupleSetTime_unr);

			TupleSet tupleSetTime_unr_last = uni.factory().range(
					uni.factory().tuple(TemporalTranslator.STATEATOM + "0" + sp + (unrolls - 1)),
					uni.factory().tuple(TemporalTranslator.STATEATOM + (steps - 1) + sp + (unrolls - 1)));
			newBounds.bound(TemporalTranslator.LOOP, tupleSetTime_unr_last);

			TupleSet trace_unr_u = uni.factory().noneOf(2);
			TupleSet trace_unr_l = uni.factory().noneOf(2);
			for (int i = 0; i < steps - 1; i++) // add the prefix to lower
				trace_unr_l.add(uni.factory().tuple(TemporalTranslator.STATEATOM + i + sp + 0,
						TemporalTranslator.STATEATOM + (i + 1) + sp + 0));
			for (int j = 0; j < unrolls; j++) {
				for (int i = 0; i < steps - 1; i++) // add the successor in non-loop
					trace_unr_u.add(uni.factory().tuple(TemporalTranslator.STATEATOM + i + sp + j,
							TemporalTranslator.STATEATOM + (i + 1) + sp + j));
				if (j < unrolls - 1)
					for (int k = 0; k < steps; k++) // add the possible successors in loop
						trace_unr_u.add(uni.factory().tuple(TemporalTranslator.STATEATOM + (steps - 1) + sp + j,
								TemporalTranslator.STATEATOM + k + sp + (j + 1)));
			}
			newBounds.bound(TemporalTranslator.PREFIX, trace_unr_l, trace_unr_u);

			if (unrolls > 1) { // otherwise no need for unrolls
				TupleSet unrollMap = uni.factory().noneOf(2);
				for (int i = 0; i < steps; i++) {
					unrollMap.add(uni.factory().tuple(new Object[] { TemporalTranslator.STATEATOM + i + sp + 0,
							TemporalTranslator.STATEATOM + i + sp + 0 }));
					for (int j = 1; j < unrolls; j++)
						unrollMap.add(uni.factory().tuple(new Object[] { TemporalTranslator.STATEATOM + i + sp + j,
								TemporalTranslator.STATEATOM + i + sp + 0 }));
				}
				newBounds.bound(TemporalTranslator.UNROLL_MAP, unrollMap, unrollMap);
			}

		} else {
			newBounds.boundExactly(TemporalTranslator.FIRST,
					uni.factory().setOf(uni.factory().tuple(TemporalTranslator.STATEATOM + "0")));
			newBounds.boundExactly(TemporalTranslator.LAST,
					uni.factory().setOf(uni.factory().tuple(TemporalTranslator.STATEATOM + "" + steps)));

			tupleSetTime_unr_first = uni.factory().range(uni.factory().tuple(TemporalTranslator.STATEATOM + "0"),
					uni.factory().tuple(TemporalTranslator.STATEATOM + steps));
			newBounds.boundExactly(TemporalTranslator.STATE, tupleSetTime_unr_first);

			TupleSet trace_unr_l = uni.factory().noneOf(2);
			for (int i = 0; i < steps; i++) // add the prefix to lower
				trace_unr_l.add(
						uni.factory().tuple(TemporalTranslator.STATEATOM + i, TemporalTranslator.STATEATOM + (i + 1)));
			newBounds.boundExactly(TemporalTranslator.PREFIX, trace_unr_l);

			newBounds.boundExactly(TemporalTranslator.L_FIRST,
					uni.factory().setOf(uni.factory().tuple(TemporalTranslator.LEVEL + "0")));
			newBounds.boundExactly(TemporalTranslator.L_LAST,
					uni.factory().setOf(uni.factory().tuple(TemporalTranslator.LEVEL + "" + (unrolls - 1))));

			TupleSet tupleSetTime_lvl = uni.factory().range(uni.factory().tuple(TemporalTranslator.LEVEL + "0"),
					uni.factory().tuple(TemporalTranslator.LEVEL + "" + (unrolls - 1)));
			newBounds.boundExactly(TemporalTranslator.LEVEL, tupleSetTime_lvl);

			TupleSet trace_lvl = uni.factory().noneOf(2);
			for (int i = 0; i < unrolls - 1; i++) // add the prefix to lower
				trace_lvl.add(uni.factory().tuple(TemporalTranslator.LEVEL + "" + i,
						TemporalTranslator.LEVEL + "" + (i + 1)));
			newBounds.boundExactly(TemporalTranslator.L_PREFIX, trace_lvl);

			TupleSet tupleSetTime_unr_last = uni.factory().range(
					uni.factory().tuple(TemporalTranslator.STATEATOM + "1"),
					uni.factory().tuple(TemporalTranslator.STATEATOM + steps));
			newBounds.bound(TemporalTranslator.LOOP, tupleSetTime_unr_last);
		}

		for (Relation r : bounds.relations()) {
			TupleSet tupleSetL = convertToUniv(bounds.lowerBound(r), uni);
			TupleSet tupleSetU = convertToUniv(bounds.upperBound(r), uni);
			if (r.isVariable()) {
				newBounds.bound(r.getExpansion(), tupleSetL.product(tupleSetTime_unr_first),
						tupleSetU.product(tupleSetTime_unr_first));
				if (bounds.target(r) != null) {
					TupleSet tupleSetT = convertToUniv(bounds.target(r), uni);
					newBounds.setTarget(r.getExpansion(), tupleSetT.product(tupleSetTime_unr_first));
				}
				if (bounds.weight(r) != null)
					newBounds.setWeight(r.getExpansion(), bounds.weight(r));
			} else {
				newBounds.bound(r, tupleSetL, tupleSetU);
				if (bounds.target(r) != null) {
					TupleSet tupleSetT = convertToUniv(bounds.target(r), uni);
					newBounds.setTarget(r, tupleSetT);
				}
				if (bounds.weight(r) != null)
					newBounds.setWeight(r, bounds.weight(r));
			}
		}
		
		for(IndexedEntry<TupleSet> entry : bounds.intBounds()) 
			newBounds.boundExactly(entry.index(), uni.factory().setOf(entry.value().iterator().next().atom(0)));

		newBounds.amalgamated = bounds.amalgamated;
		newBounds.trivial_config = bounds.trivial_config;
		newBounds.integrated = bounds.integrated;
		newBounds.integration = bounds.integration;

		if (bounds.amalgamated() != null) {
			PardinusBounds newAmalg = expand(bounds.amalgamated(), uni, steps, unrolls);
			newBounds = new PardinusBounds(newBounds, newAmalg);
		}

		return newBounds;
	}
	
	/**
	 * Exactly binds relations up to a certain trace length to the values of a
	 * provided instance.
	 * 
	 * NOTE: this is re-doing part of the job already doen previously by
	 * {@link #expand(PardinusBounds, int, int)} to extBounds, refactor.
	 * 
	 * @param tmpBounds the original, non expanded bounds
	 * @param extBounds the extended state idiom bounds
	 * @param prefxLen  the length of the prefix to bind exactly
	 * @param traceLen  the total trace length
	 * @param inst      the instance from which to bind
	 * @return
	 */
	// [HASLab] explorer
	public static Bounds extend(PardinusBounds tmpBounds, Bounds extBounds, int prefxLen, int traceLen, TemporalInstance inst) {
		if (!TemporalTranslator.ExplicitUnrolls)
			throw new UnsupportedOperationException();
		Universe u = extBounds.universe();
		for (Relation r : tmpBounds.relations()) {
			if (r.isVariable()) {
				int i;
				TupleSet upp = u.factory().noneOf(r.arity()+1);
				TupleSet low = u.factory().noneOf(r.arity()+1);
				for (i = 0; i < traceLen && i < prefxLen; i++) {
					Evaluator eval = new Evaluator(inst);
					TupleSet time = u.factory().setOf(TemporalTranslator.STATEATOM + i + TemporalTranslator.STATE_SEP + 0);
					TupleSet ts = eval.evaluate(r,i);
					low.addAll(convertToUniv(ts,u).product(time));
					upp.addAll(convertToUniv(ts,u).product(time));
				}
				for (; i < traceLen; i++) {
					TupleSet tupleSetL = convertToUniv(tmpBounds.lowerBound(r), u);
					TupleSet tupleSetU = convertToUniv(tmpBounds.upperBound(r), u);

					TupleSet time = u.factory().setOf(TemporalTranslator.STATEATOM + i + TemporalTranslator.STATE_SEP + 0);

					low.addAll(tupleSetL.product(time));
					upp.addAll(tupleSetU.product(time));
				}
				extBounds.bound(r.getExpansion(), low, upp);
			} else {
				if (prefxLen > 0)
					if (inst.contains(r)) { // due to reified atoms
						Evaluator eval = new Evaluator(inst);
						TupleSet ts = eval.evaluate(r);
						extBounds.boundExactly(r, convertToUniv(ts,u));			
					}
			}
		}

		return extBounds;
	}
	
	/**
	 * TODO
	 * 
	 * @param tmpBounds
	 * @param extBounds
	 * @param prefxLen
	 * @param traceLen
	 * @param inst
	 * @param excepts relations that will be bound exactly to this tuple set.
	 * @return
	 */
	public static Bounds extend(PardinusBounds tmpBounds, Bounds extBounds, int prefxLen, int traceLen, TemporalInstance inst, Map<Relation,TupleSet> excepts) {
		if (!TemporalTranslator.ExplicitUnrolls)
			throw new UnsupportedOperationException();
		Universe u = extBounds.universe();
		Evaluator eval = new Evaluator(inst);
		for (Relation r : tmpBounds.relations()) {
			TupleSet tupleSetL = convertToUniv(tmpBounds.lowerBound(r), u);
			TupleSet tupleSetU = convertToUniv(tmpBounds.upperBound(r), u);
			if (r.isVariable()) {
				int i;
				TupleSet upp = u.factory().noneOf(r.arity()+1);
				TupleSet low = u.factory().noneOf(r.arity()+1);
				for (i = 0; i < traceLen-1 && i < prefxLen-1; i++) {
					TupleSet time = u.factory().setOf(TemporalTranslator.STATEATOM + i + TemporalTranslator.STATE_SEP + 0);
					TupleSet ts = eval.evaluate(r,i);
					low.addAll(convertToUniv(ts,u).product(time));
					upp.addAll(convertToUniv(ts,u).product(time));
				}
				
				if (i < traceLen && i < prefxLen) {
					if (excepts.containsKey(r)) {
						TupleSet time = u.factory().setOf(TemporalTranslator.STATEATOM + i + TemporalTranslator.STATE_SEP + 0);
						low.addAll(convertToUniv(excepts.get(r),u).product(time));
						upp.addAll(convertToUniv(excepts.get(r),u).product(time));
					} else {
						TupleSet time = u.factory().setOf(TemporalTranslator.STATEATOM + i + TemporalTranslator.STATE_SEP + 0);
						TupleSet ts = eval.evaluate(r,i);
						low.addAll(convertToUniv(ts,u).product(time));
						upp.addAll(convertToUniv(ts,u).product(time));
					}
					i++;
				}
				for (; i < traceLen; i++) {
					TupleSet time = u.factory().setOf(TemporalTranslator.STATEATOM + i + TemporalTranslator.STATE_SEP + 0);

					low.addAll(tupleSetL.product(time));
					upp.addAll(tupleSetU.product(time));
				}
				extBounds.bound(r.getExpansion(), low, upp);
			} else {
				if (inst.contains(r)) { // due to reified atoms
					if (prefxLen == 0) { // only way to have these changed
						if (excepts.containsKey(r)) {
							extBounds.bound(r, convertToUniv(excepts.get(r),u), convertToUniv(excepts.get(r),u));
						} else {
							extBounds.bound(r, tupleSetL, tupleSetU);
						}
					}
					else {
						TupleSet ts = eval.evaluate(r);
						extBounds.boundExactly(r, convertToUniv(ts,u));			
					}
				}
			}
		}

		return extBounds;
	}

	/**
	 * Creates a new universe by duplicating the original one and creating a given
	 * number of {@link TemporalTranlator#STATE state} atoms, unrolled a certain
	 * number of times.
	 * 
	 * Guarantees that the first steps*unrolls atoms are the ordered state atoms.

	 * @assumes unrolls > 0
	 * @assumes states > 0
	 * @param oldUniverse
	 *            the original universe.
	 * @param steps
	 *            the number of distinguished states in the trace.
	 * @param unrolls
	 *            the number of trace unrolls.
	 * @return a new universe with the state atoms plus the original ones.
	 * @throws IllegalArgumentException
	 *             unrolls < 1 || states < 1
	 */
	static public Universe expandUniverse(Universe oldUniverse, int steps, int unrolls) {
		if (unrolls < 1 || steps < 1)
			throw new IllegalArgumentException("Number of unrolls or steps <1.");

		List<Object> newAtoms = new ArrayList<Object>();

		if (TemporalTranslator.ExplicitUnrolls) {
			for (int j = 0; j < unrolls; j++)
				for (int i = 0; i < steps; i++) {
					Object x = TemporalTranslator.STATEATOM + i + TemporalTranslator.STATE_SEP + j;
					newAtoms.add(x);
				}
		} else {
			for (int i = 0; i <= steps; i++) {
				Object x = TemporalTranslator.STATEATOM + i;
				newAtoms.add(x);
			}
			for (int j = 0; j < unrolls; j++) {
				Object x = TemporalTranslator.LEVEL + "" + j;
				newAtoms.add(x);
			}
		}

		Iterator<Object> it = oldUniverse.iterator();
		while (it.hasNext())
			newAtoms.add(it.next());

		return new Universe(newAtoms);
	}

	/**
	 * Converts an existing tuple set into an identical tuple set with a different
	 * universe.
	 * 
	 * @param tset
	 *            the existing tuple set from the old universe.
	 * @param universe
	 *            the new universe.
	 * @return the converted tuple set.
	 */
	static public TupleSet convertToUniv(TupleSet tset, Universe universe) {
		TupleSet tupleSet = universe.factory().noneOf(tset.arity());
		Iterator<Tuple> itr = tset.iterator();
		while (itr.hasNext()) {
			Tuple t = itr.next();
			List<Object> l = new ArrayList<Object>();
			for (int i = 0; i < t.arity(); i++)
				l.add(t.atom(i));
			tupleSet.add(universe.factory().tuple(l));
		}
		return tupleSet;
	}

}