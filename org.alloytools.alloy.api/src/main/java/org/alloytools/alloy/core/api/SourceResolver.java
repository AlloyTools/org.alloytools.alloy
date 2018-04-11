package org.alloytools.alloy.core.api;

import java.io.IOException;

/**
 * A content resolver for translating names to content. This is for example
 * useful if some files are in a window instead of on disk. Can also provide
 * caching if so desired.
 */
public interface SourceResolver {
	String resolve(String path) throws IOException;
}
