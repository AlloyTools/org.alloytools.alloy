package org.alloytools.alloy.solver.api;

import org.alloytools.alloy.core.api.TSig;

public interface IAtom extends Comparable<IAtom> {
	AlloySolution getSolution();

	TSig getSig();

	Object getValue();

	ITupleSet asTupleSet();

	int getIndex();

	default ITupleSet join(ITupleSet right) {
		return asTupleSet().join(right);
	}

	default ITupleSet product(ITupleSet right) {
		return asTupleSet().product(right);
	}

	default ITupleSet head() {
		return asTupleSet();
	}

	default ITupleSet tail() {
		return getSolution().none();
	}

	public String getName();
	
	default int toInt() {
		return Integer.parseInt(getName()); 
	}
}
