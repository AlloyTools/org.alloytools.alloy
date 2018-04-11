package org.alloytools.alloy.core.api;

/**
 * A Field in a sig
 */
public interface TField {
	/**
	 * The type of this relation
	 * 
	 * @return the type of this relation
	 */
	TRelationType getType();
	
	/**
	 * Parent type (not sure this is needed?)
	 * 
	 * @return the parent type
	 */
	TSig getParent();

	/**
	 * The name of the field
	 */
	String getName();
}
