package org.alloytools.alloy.core.api;

import java.nio.file.Path;
import java.util.List;
import java.util.Optional;

import org.alloytools.alloy.solver.api.AlloySolver;

/**
 * Primary interface into Alloy.
 */
public interface Alloy {
	/**
	 * Get a list of available solvers
	 * 
	 * @return a list of available solvers
	 */
	List<AlloySolver> getSolvers();

	Optional<AlloySolver> getSolver(String id);
	
	/**
	 * Return the compiler but providing a resolver for abstracting where the
	 * content is coming from.
	 * 
	 * @param resolver
	 *            abstracts the file system
	 * @return an Alloy compiler
	 */
	AlloyCompiler compiler(SourceResolver resolver);

	/**
	 * Return a default compiler based on the current file system
	 * 
	 * @return a compiler
	 */
	AlloyCompiler compiler();
	
	Path getFile(String pathWithSlashes);
}
