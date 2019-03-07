package org.alloytools.alloy.core.api;

import java.util.List;

/**
 * A Field in a sig
 */
public interface TField {
	/**
	 * The type of this relation.
	 * 
	 * @return the type of this relation
	 */
	List<TColumnType> getType();
	
	/**
	 * Parent type 
	 * 
	 * TODO (not sure this is needed?)
	 * 
	 * @return the parent type
	 */
	TSig getParent();

	/**
	 * The name of the field
	 */
	String getName();
}
