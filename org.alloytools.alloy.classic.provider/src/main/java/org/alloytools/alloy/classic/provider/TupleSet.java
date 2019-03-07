package org.alloytools.alloy.classic.provider;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import org.alloytools.alloy.core.api.Solution;
import org.alloytools.alloy.core.api.IAtom;
import org.alloytools.alloy.core.api.IRelation;
import org.alloytools.alloy.core.api.ITuple;

public class TupleSet implements IRelation {

	final Solution	solution;
	final int			arity;
	final ITuple[]		tuples;

	TupleSet(Solution solution, int arity, Tuple[] tuples) {
		this.solution = solution;
		this.tuples = tuples;
		this.arity = arity;
	}

	public TupleSet(Solution solution, int arity, List<? extends IAtom> atoms) {
		this(solution, arity, toTuples(solution, arity, atoms));
	}

	@Override
	public int arity() {
		return arity;
	}

	@Override
	public IRelation join(IRelation right) {

		assert solution == right.getSolution();

		int arity = this.arity() + right.arity() - 2;
		List<IAtom> atoms = new ArrayList<>();

		for (ITuple l : this) {
			IAtom last = l.last();

			for (ITuple r : right) {
				IAtom first = r.first();

				if (last == first) {

					for (int i = 0; i < l.arity() - 1; i++) {
						atoms.add(l.get(i));
					}

					for (int i = 1; i < r.arity(); i++) {
						atoms.add(r.get(i));
					}

				}
			}
		}

		return new TupleSet(solution, arity, atoms);
	}

	@Override
	public IRelation product(IRelation right) {

		assert solution == right.getSolution();

		List<IAtom> atoms = new ArrayList<>();
		int arity = this.arity() + right.arity();
		for (ITuple l : this) {

			for (ITuple r : right) {

				for (int i = 0; i < l.arity(); i++) {
					atoms.add(l.get(i));
				}
				for (int i = 0; i < r.arity(); i++) {
					atoms.add(r.get(i));
				}
			}
		}
		return new TupleSet(solution, arity, atoms);
	}

	@Override
	public TupleSet head() {
		return split(0, 1);
	}

	private TupleSet split(int from, int to) {

		assert from > 0;
		assert from < to;
		assert to > from;
		assert to <= arity;

		List<IAtom> atoms = new ArrayList<>();
		for (ITuple tuple : this) {
			for (int i = from; i < to; i++)
				atoms.add(tuple.get(i));
		}
		return new TupleSet(solution, to - from, atoms);
	}

	@Override
	public IRelation tail() {
		return split(1, arity);
	}

	@Override
	public Iterator<ITuple> iterator() {
		return Arrays.stream(tuples)
			.iterator();
	}

	@Override
	public int size() {
		return tuples.length;
	}

	@Override
	public Solution getSolution() {
		return solution;
	}

	static Tuple[] toTuples(Solution solution, int arity, List<? extends IAtom> atoms) {
		Set<Tuple> removeDuplicates = new HashSet<>();
		for (int i = 0; i < atoms.size(); i += arity) {
			int base = i;
			Tuple tuple = new Tuple(solution) {

				@Override
				public int arity() {
					return arity;
				}

				@Override
				public IAtom get(int i) {
					return atoms.get(base + i);
				}

			};
			removeDuplicates.add(tuple);
		}
		ArrayList<Tuple> list = new ArrayList<>(removeDuplicates);
		Collections.sort(list);
		Tuple[] result = removeDuplicates.toArray(new Tuple[removeDuplicates.size()]);
		Arrays.sort(result);
		return result;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();

		sb.append("{ ");

		String del = "";
		for (ITuple tuple : tuples) {
			sb.append(del);
			sb.append(tuple);
			del = ", ";
		}

		sb.append(" }");
		return sb.toString();
	}

	public IRelation toIdent() {

		List<IAtom> atoms = new ArrayList<>();
		for (ITuple t : this) {
			atoms.add(t.first());
			atoms.add(t.first());
		}
		return new TupleSet(solution, 2, atoms);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + arity;
		result = prime * result + Arrays.hashCode(tuples);
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		TupleSet other = (TupleSet) obj;
		if (arity != other.arity)
			return false;
		if (!Arrays.equals(tuples, other.tuples))
			return false;
		return true;
	}

}
