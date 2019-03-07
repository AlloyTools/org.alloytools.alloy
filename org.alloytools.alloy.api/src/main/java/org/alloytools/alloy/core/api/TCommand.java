
package org.alloytools.alloy.core.api;

import java.util.Set;

public interface TCommand {

	enum Expects {
		UNKNOWN, SATISFIED, UNSATISFIED
	}

	/**
	 * The name of the command
	 */
	String getName();

	/**
	 * Set scopes on the command
	 * 
	 * @return get the sig scopes in this command
	 */
	Set<TScope> getScopes();

	/**
	 * Answer the expects part of the run. The expects predicts if the run
	 * should have a solution or not. If not specified, {@link Expects#UNKNOWN}
	 * is returned.
	 * 
	 * @return expects
	 */
	Expects getExpects();

	/**
	 * Get the associated module.
	 * 
	 * @return the module
	 */
	Module getModule();
}
