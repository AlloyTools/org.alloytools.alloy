package org.alloytools.alloy.core.api;

import java.io.File;

/**
 * An Alloy Compiler that can compile a file or a source
 */
public interface AlloyCompiler {
	/**
	 * Compile a source string into a module
	 * 
	 * @return a Module
	 */
	AlloyModule compileSource(String source) throws Exception;

	/**
	 * Compile a path, the path is resolved via the resolver. Any opens in the
	 * content will be also recursively compiled.
	 * 
	 * @return a Module
	 */
	AlloyModule compile(String path) throws Exception;

	/**
	 * Compile a file. Any opens in the content will be also recursively
	 * compiled.
	 * 
	 * @param file
	 *            the file
	 * @return a Module
	 */
	AlloyModule compile(File file) throws Exception;
}
