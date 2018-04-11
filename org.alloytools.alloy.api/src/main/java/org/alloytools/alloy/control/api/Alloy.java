package org.alloytools.alloy.control.api;

import java.util.List;

import org.alloytools.alloy.core.api.AlloyCompiler;
import org.alloytools.alloy.core.api.SourceResolver;
import org.alloytools.alloy.solver.api.AlloySolver;

/**
 * Primary interface into Alloy.
 */
public interface Alloy {
	/**
	 * Get a list of available solvers
	 * 
	 * @return a lost of available solvers
	 */
	List<AlloySolver> getSolvers();

	/**
	 * Return the default solver
	 * 
	 * @return the default solver
	 */
	AlloySolver getDefaultSolver();

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
}
