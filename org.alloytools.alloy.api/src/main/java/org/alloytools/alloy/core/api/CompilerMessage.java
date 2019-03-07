package org.alloytools.alloy.core.api;

/**
 * A warning or error from the compilation
 */
public interface CompilerMessage {
	/**
	 * The actual message
	 * 
	 * @return the messsage
	 */
	String getMessage();

	/**
	 * The total source code of the module
	 * 
	 * @return the source code
	 */
	String getSource();

	/**
	 * The path to the source code. This path must be interpreted through the
	 * compiler used to compile the module since some sources are in user
	 * interface components.
	 * 
	 * @return the path to the source code
	 */
	String getPath();

	/**
	 * The line number in the source code of the offending code
	 * 
	 * @return line number
	 */
	int line();

	/**
	 * The column number in the source code of the offending code
	 * 
	 * @return column number
	 */
	int column();

	/**
	 * The number of characters of the offending code
	 */
	int span();
}
