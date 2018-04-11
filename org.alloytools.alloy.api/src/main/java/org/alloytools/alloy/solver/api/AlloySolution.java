package org.alloytools.alloy.solver.api;

import org.alloytools.alloy.core.api.TSig;

public interface AlloySolution extends Iterable<AlloyInstance> {

	boolean isSatisfied();

     ITupleSet none();

}
