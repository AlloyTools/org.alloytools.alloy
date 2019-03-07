package org.alloytools.alloy.core.api;

import java.util.stream.Stream;
import java.util.stream.StreamSupport;

/**
 * A solution is the answer of a solver. It can either be satisfied or not. If
 * it is satisfied then you can ask for the _instances_.
 * 
 */
public interface Solution extends Iterable<Instance> {

	/**
	 * Return the solver that created this solution
	 * 
	 * @return the solver that created this solution
	 */
	Solver getSolver();

	/**
	 * Return the solver that created this solution
	 * 
	 * @return the solver that created this solution
	 */
	SolverOptions getOptions();

	/**
	 * Return the module that was used for this solution
	 * 
	 * @return the module that was used this solution
	 */
	Module getModule();

	/**
	 * Answer the command that was used for this solution
	 * 
	 * @return the command that was used for this solution
	 */
	TCommand getCommand();

	/**
	 * Answer if this solution is satisfied.
	 */
	boolean isSatisfied();

	/**
	 * Provides access to a root tupleset which can be used to create new
	 * tuplesets.
	 * 
	 * @return a tuple set representing none.
	 */
	IRelation none();

	/**
	 * Turn this solution into a stream of instances.
	 * 
	 * @return a stream of instances
	 */
	default Stream<Instance> stream() {
		return StreamSupport.stream(this.spliterator(), false);
	}
}
