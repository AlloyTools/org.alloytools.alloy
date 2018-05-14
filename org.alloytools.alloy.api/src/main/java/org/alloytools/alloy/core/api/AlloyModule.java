package org.alloytools.alloy.core.api;

import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * Represents an Alloy Module
 */
public interface AlloyModule {

	/**
	 * The source path of this module. In certain cases
	 * 
	 * @return
	 */
	Optional<String> getPath();

	/**
	 * Get the defined sigs in this module
	 * 
	 * @return a list of sigs
	 */
	Set<TSig> getSigs();

	/**
	 * Get a sig by name
	 * 
	 * @param name
	 *            the name of the request sig
	 * @return an optional TSig
	 */
	Optional<TSig> getSig(String name);

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

	List<CompilerMessage> getWarnings();

	List<CompilerMessage> getErrors();

	boolean isValid();


	Map<String, String> getSourceOptions(TCommand command);
}
