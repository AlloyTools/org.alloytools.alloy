package org.alloytools.alloy.core.api;

import java.util.List;
import java.util.Optional;

/**
 * Represents a signature in Alloy.
 */
public interface TSig {
	/**
	 * The name of the signature
	 * 
	 * @return the name of the signature.
	 */
	String getName();

	/**
	 * The field relations associated with the signature
	 * 
	 * @return the fields
	 */
	List<? extends TField> getFields();

	/**
	 * Get a particular field
	 * 
	 * @param fieldName
	 *            the field name
	 * @return an optional field
	 */
	Optional<? extends TField> getTField(String fieldName);
}
