package org.alloytools.alloy.core.api;

import java.io.File;
import java.util.List;
import java.util.Optional;

/**
 * Primary interface into Alloy. An instance can be found through the Java
 * {@link java.util.ServiceLoader}
 * <p>
 * This class is the root into Alloy. It provides access to the solvers, the
 * compiler, and
 */
public interface Alloy {
	/**
	 * Get a list of available solvers
	 * 
	 * @return a list of available solvers
	 */
	List<Solver> getSolvers();

	/**
	 * Get a solver with a specific name
	 * 
	 * @param id
	 *            the name of the solver
	 * @return and optional AlloySolver
	 */
	Optional<Solver> getSolver(String id);

	/**
	 * Return the compiler but providing a resolver for abstracting where the
	 * content is coming from.
	 * 
	 * @param resolver
	 *            abstracts the file system
	 * @return an Alloy compiler
	 */
	Compiler compiler(SourceResolver resolver);

	/**
	 * Return a list of visualizers that can render an {@link Instance}
	 * 
	 * @return a list of visualizers
	 */
	List<Visualizer> getVisualizers();

	/**
	 * Return a default compiler based on the current file system
	 * 
	 * @return a compiler
	 */
	Compiler compiler();

	/**
	 * 
	 */

	/**
	 * Get a file in the Alloy private directory. The intention for this path is
	 * to be used by solvers or visualizers for caches and preferences.
	 * 
	 * @param pathWithSlashes a path separated with slashes also on windows
	 * @return a Path to a file on the file system using slashes to separate
	 *         directories.
	 */

	File getPreferencesDir(String id);
}
