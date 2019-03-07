package org.alloytools.alloy.core.api;

/**
 * A scope regulates the A scope setting on a command (check/run)
 * 
 * TODO does this need a start and ending scope like the original?
 */
public interface TScope {
	/**
	 * The signature for which this scope is set
	 */
	TSig getSig();

	/**
	 * The maximum number of atoms for this sig
	 */
	int size();

	/**
	 * If this is an exact or growing scope
	 */
	boolean isExact();
}
