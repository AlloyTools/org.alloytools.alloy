package org.alloytools.alloy.core.api;

/**
 * An atom is an immutable object that has no meaning. Atoms always belong to a
 * single Alloy Solution and cannot be used across solutions. However, the same
 * atoms are used across Alloy Instances.
 */
public interface IAtom extends Comparable<IAtom> {

	/**
	 * Return a human readble name for the atom that is unique for all atoms of
	 * the solution.
	 * 
	 * @return the unique name of the atom
	 */
	String getName();

	/**
	 * Get the owning solution
	 * 
	 * @return the owner of the atom
	 */
	Solution getSolution();

	/**
	 * Get the signature of this atom
	 * 
	 * @return the signature
	 */
	TSig getSig();

	/**
	 * Convert the atom to an ITupleSet
	 * 
	 * @return a tupleset with one atom
	 */
	IRelation asTupleSet();

	/**
	 * Each atom has a unique index int the universe.
	 * 
	 * TODO necessary?
	 * 
	 * @return the universe index
	 */
	int getIndex();

	/**
	 * Join this atom with a tuple set
	 * 
	 * @param right
	 *            the tuple set to join with
	 * @return a new tuple set that is the Alloy join of this and the right
	 */
	default IRelation join(IRelation right) {
		return asTupleSet().join(right);
	}

	/**
	 * Create the product atom with a tuple set
	 * 
	 * @param right
	 *            the tuple set to create the product with
	 * @return a new tuple set that is the Alloy product of this and the right
	 */
	default IRelation product(IRelation right) {
		return asTupleSet().product(right);
	}

	/**
	 * Provides a new tupleset with itself
	 * 
	 * @return a tupleset of itself
	 */
	default IRelation head() {
		return asTupleSet();
	}

	/**
	 * An empty tuple set
	 * 
	 * @return an empty tuple set
	 */
	default IRelation tail() {
		return getSolution().none();
	}

	/**
	 * See {@link #equals(Object)}
	 * 
	 * @return a hashcode
	 */
	int hashCode();

	/**
	 * Equality is when the other object has identity equality
	 * 
	 * @return true if the other atom == this atom
	 */
	boolean equals(Object o);

	/**
	 * Return the int value, assuming this atom is an Int. This will throw a
	 * Runtime Exception if the atom is not an Int
	 */
	int toInt();
}
