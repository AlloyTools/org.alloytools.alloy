package org.alloytools.alloy.core.api;

/**
 * A list of atoms.
 */
public interface ITuple extends Comparable<ITuple> {

	/**
	 * Number of atoms in the tuple.
	 * 
	 * @return the width of this tuple
	 */
	int arity();

	/**
	 * Get the n'th (starting at 0) atom in this tuple. n must be less than the
	 * arity.
	 * 
	 * @param n
	 *            the index
	 * @return the atom
	 */
	IAtom get(int n);

	/**
	 * Return the last atom of this tuple. The tuple must be non-empty
	 * 
	 * @return the last atom
	 */
	default IAtom last() {
		return get(arity() - 1);
	}

	/**
	 * Return the first atom of this tuple. The tuple must be non-empty
	 * 
	 * @return the first atom
	 */
	default IAtom first() {
		return get(0);

	}

	/**
	 * Return this Tuple as a tuple set.
	 * 
	 * @return a tuple set
	 */

	IRelation asTupleSet();

	/**
	 * See {@link #equals(Object)}
	 * 
	 * @return a hashcode
	 */
	int hashCode();

	/**
	 * Equality is when the other tuple has the same arity . Notice that atoms
	 * belong to a solution, it is therefore impossible to compare tuples from
	 * different solutions.
	 * 
	 * @return true if the other ITuple is equal.
	 */
	boolean equals(Object o);

}
