package org.alloytools.alloy.solver.api;

public interface ITuple extends Comparable<ITuple> {
	
	int arity();

    IAtom get(int n);

	default IAtom last() {
		return get(arity()-1);
	}

	default IAtom first() {
		return get(0);
		
	}
	
	ITupleSet asTupleSet();
	
}
