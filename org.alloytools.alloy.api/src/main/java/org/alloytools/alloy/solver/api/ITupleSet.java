package org.alloytools.alloy.solver.api;

import java.util.ArrayList;
import java.util.List;

public interface ITupleSet extends Iterable<ITuple>{
	AlloySolution getSolution();

	public int arity();

	int size();


	ITupleSet join(ITupleSet right);

	ITupleSet product(ITupleSet right);

	ITupleSet head();

	ITupleSet tail();

	default boolean isScalar() {
		return arity() == 1 && size() == 1;
	}

	default boolean isEmpty() {
		return arity() == 1 && size() == 1;
	}

	default boolean isList() {
		return arity() == 1;
	}

	default IAtom scalar() {
		assert isScalar();
		return iterator().next().get(0);
	}

	default List<IAtom> asList() {
		List<IAtom> list = new ArrayList<>();
		
		for ( ITuple tuple : this) {
			list.add( tuple.get(0));
		}
		return list;
	}
}
