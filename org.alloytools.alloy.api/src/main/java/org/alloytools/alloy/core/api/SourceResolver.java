package org.alloytools.alloy.core.api;

/**
 * A content resolver for translating names to content. This is for example
 * useful if some files are in a window instead of on disk. Can also provide
 * caching if so desired.
 */
public interface SourceResolver {
	/**
	 * Resolve a path to a source string
	 * 
	 * @param path
	 *            the path referenced in an Alloy file
	 * @return the content associated with the given path
	 */
	String resolve(String path) ;
}
