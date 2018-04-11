package org.alloytools.alloy.core.api;

import java.util.List;
import java.util.Optional;

/**
 * Represents an Alloy Module
 */
public interface AlloyModule {

	/**
	 * Get the defined sigs in this module
	 * 
	 * @return a list of sigs
	 */
	List<TSig> getSigs();

	/**
	 * Get a sig by name
	 * 
	 * @param name
	 *            the name of the request sig
	 * @return an optional TSig
	 */
	Optional<? extends TSig> getSig(String name);

	/**
	 * Get any run commands defined in the module
	 * 
	 * @return the list of available run commands
	 */
	List<TRun> getRuns();

	/**
	 * Get any check commands defined in the module
	 * 
	 * @return the list of available check commands
	 */
	List<TCheck> getChecks();

}
