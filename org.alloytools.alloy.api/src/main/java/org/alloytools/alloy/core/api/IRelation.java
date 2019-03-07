package org.alloytools.alloy.core.api;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

/**
 * An IRelation is a matrix of {@link IAtom}s. The {@link #arity()} is the width
 * of the relation and the {@link #size()} is the length of the relation. An
 * IRelation always belongs to an {@link Solution}. A row in the relation
 * is called a <em>tuple</em>.
 */
public interface IRelation extends Iterable<ITuple> {

	/**
	 * The solution this set belongs to
	 * 
	 * @return the alloy solution
	 */
	Solution getSolution();

	/**
	 * The arity of this tuple set, also called the width.
	 * 
	 * @return the arity
	 */
	public int arity();

	/**
	 * The size of the matrix or also called the height.
	 * 
	 * @return the size of the tuple set
	 */
	int size();

	/**
	 * Join this atom with a tuple set
	 * 
	 * @param right
	 *            the tuple set to join with
	 * @return a new tuple set that is the Alloy join of this and the right
	 */
	IRelation join(IRelation right);

	/**
	 * Create the product atom with a tuple set
	 * 
	 * @param right
	 *            the tuple set to create the product with
	 * @return a new tuple set that is the Alloy product of this and the right
	 */
	IRelation product(IRelation right);

	/**
	 * Provides a new tupleset with the left column
	 * 
	 * @return a tupleset of itself
	 */
	IRelation head();

	/**
	 * An new tuple set that is equal to this tuple set but lacks the first
	 * column
	 * 
	 * @return a tuple set
	 */
	IRelation tail();

	/**
	 * Since Alloy stores all atoms as tuple sets also simple scalars are stored
	 * that way. This provides an easy check to see if the tupleset only holds 1
	 * scalar.
	 * 
	 * @return is this tuple set a scalar?
	 */
	default boolean isScalar() {
		return arity() == 1 && size() == 1;
	}

	/**
	 * Is this tupleset empty?
	 * 
	 * @return true if this tuple set is empty
	 */
	default boolean isEmpty() {
		return arity() == 0 && size() == 0;
	}

	/**
	 * Is this tuple set arity 1?
	 * 
	 * @return true if this tuple set has arity 1
	 */
	default boolean isList() {
		return arity() == 1;
	}

	/**
	 * If this tuple sets holds a single scalar then this method returns the
	 * scalar.
	 * 
	 * @return the scalar value
	 */
	default Optional<IAtom> scalar() {
		if (isScalar()) {
			return Optional.of(iterator().next().get(0));
		}
		return Optional.empty();
	}

	/**
	 * Return the most left column as a list of atoms
	 * 
	 * @return a list of atoms
	 */
	default List<IAtom> asList() {
		assert isList();

		List<IAtom> list = new ArrayList<>();

		for (ITuple tuple : this) {
			list.add(tuple.get(0));
		}
		return list;
	}

	/**
	 * See {@link #equals(Object)}
	 * 
	 * @return a hashcode
	 */
	int hashCode();

	/**
	 * Equality is when the other tuple set has the same arity and the identical
	 * atoms. Notice that atoms belong to a solution, it is therefore impossible
	 * to compare tuplesets from different solutions.
	 * 
	 * @return true if the other ITupleSet is equal.
	 */
	boolean equals(Object o);
}
