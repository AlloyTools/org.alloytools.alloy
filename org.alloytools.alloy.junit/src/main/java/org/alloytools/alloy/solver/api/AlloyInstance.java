package org.alloytools.alloy.solver.api;

import org.alloytools.alloy.core.api.TField;
import org.alloytools.alloy.core.api.TSig;

public interface AlloyInstance {

	ITupleSet getField(TField field);

	ITupleSet getAtoms(TSig sig);

}
