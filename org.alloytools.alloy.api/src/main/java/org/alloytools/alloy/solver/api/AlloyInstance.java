package org.alloytools.alloy.solver.api;

import org.alloytools.alloy.core.api.TField;
import org.alloytools.alloy.core.api.TSig;

public interface AlloyInstance {

	ITupleSet getField(TField field);

	ITupleSet getAtoms(TSig sig);

	ITupleSet getVariable(String func, String var);

	ITupleSet eval(String cmd);

	ITupleSet universe();

	ITupleSet ident();

}
