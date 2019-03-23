package org.alloytools.alloy.core.api;

import java.util.stream.Stream;
import java.util.stream.StreamSupport;

/**
 * A solution is produced by a {@link Solver}. It can either be satisfiable or
 * not. Only a satisfiable solution contains instances.
 */
public interface Solution extends Iterable<Instance> {

	/**
	 * The solver that produced this solution
	 * 
	 * @return the solver that produced this solution
	 */
	Solver getSolver();

	/**
	 * The options used when solving for this solution
	 * 
	 * @return the options used when solving for this solution
	 */
	SolverOptions getOptions();

	/**
	 * The module this solution was derived from.
	 * 
	 * @return the module this solution was derived from.
	 */
	Module getModule();

	/**
	 * The command this is a solution to
	 * 
	 * @return the command this is a solution to
	 */
	TCommand getCommand();

	/**
	 * Whether the specification was satisfiable or not.
	 */
	boolean isSatisfied();

	/**
	 * Returns an empty relation.
	 * 
	 * @return an empty relation.
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
