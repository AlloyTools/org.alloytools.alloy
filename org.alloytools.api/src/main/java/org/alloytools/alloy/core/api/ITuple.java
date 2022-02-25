package org.alloytools.alloy.core.api;

/**
 * A list of atoms.
 */
public interface ITuple extends Comparable<ITuple>, Iterable<IAtom> {

    /**
     * Number of atoms in the tuple. A tuple must contain at least one atom, hence
     * the arity must be positive
     *
     * @return the arity of this tuple
     */
    int arity();

    /**
     * Get the n'th (starting at 0) atom in this tuple. n must be less than the
     * arity.
     *
     * @param n the index
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
     * Return this tuple as a relation
     *
     * @return a tuple set
     */
    IRelation asRelation();

    /**
     * See {@link #equals(Object)}
     *
     * @return a hash code
     */
    @Override
    int hashCode();

    /**
     * Two tuples are equal if they have the same arity and they have matching atoms
     * at each each position (from 0 to arity-1).
     *
     * @return true if equal to {@code o}
     */
    @Override
    boolean equals(Object o);

}
