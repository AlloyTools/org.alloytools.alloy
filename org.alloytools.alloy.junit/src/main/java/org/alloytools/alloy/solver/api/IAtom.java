package org.alloytools.alloy.solver.api;

import org.alloytools.alloy.core.api.TSig;

public interface IAtom {
	TSig getSig();

	ITupleSet join(ITupleSet tuples);

	Object getValue();
}
