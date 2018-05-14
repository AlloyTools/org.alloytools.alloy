package org.alloytools.alloy.solver.api;

public interface AlloySolution extends Iterable<AlloyInstance> {

	boolean isSatisfied();

     ITupleSet none();

}
