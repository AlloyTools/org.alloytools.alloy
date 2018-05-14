package org.alloytools.alloy.solver.api;

import java.util.List;

public interface ITuple extends List<IAtom> {
	ITuple product(ITuple tuple);

	int arity();

	ITuple prepend(IAtom atom);

	ITuple append(IAtom atom);
	
    ITuple join(ITuple that);

    IAtom head();

    List<IAtom> tail();
    
    /**
     * Returns the subtuple containing the first n atoms (n must be between 1 and
     * arity)
     */
    List<ITuple> head(int n);

    /**
     * Returns the subtuple containing the last n atoms (n must be between 1 and
     * arity)
     */
    List<ITuple> tail(int n);

}
