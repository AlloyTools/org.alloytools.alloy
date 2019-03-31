package org.alloytools.alloy.core.api;

/**
 * An atom is an immutable object that has no meaning. Atoms always belong to a
 * single Alloy Solution and cannot be used across solutions. However, the same
 * atoms are reused across Alloy Instances.
 */
public interface IAtom extends Comparable<IAtom> {

    /**
     * Return a human readable name for the atom that is unique for all atoms of the
     * solution.
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
     * Convert the atom to a {@link IRelation}
     * 
     * @return a unary singleton relation containing only this atom
     */
    IRelation asTupleSet();

    /**
     * Each atom has a unique index the universe. TODO necessary?
     * 
     * @return the index of this atom in the Alloy universe
     */
    int getIndex();

    /**
     * Join this atom with a relation
     * 
     * @param right the relation to join with
     * @return the result of the join
     */
    default IRelation join(IRelation right) {
        return asTupleSet().join(right);
    }

    /**
     * Create the product of this atom with a given relation
     * 
     * @param right the relation to create the product with
     * @return the result of the product
     */
    default IRelation product(IRelation right) {
        return asTupleSet().product(right);
    }

    /**
     * The same as {@link IAtom#asTupleSet()}
     * 
     * @return a unary singleton relation containing only this atom
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
     * @return a hash code of this atom
     */
    int hashCode();

    /**
     * Equality is when the other object has identity equality
     * 
     * @return true if the other atom == this atom
     */
    boolean equals(Object o);

    /**
     * Return the integer value, assuming this atom is an integer. Throws a
     * {@link RuntimeException} if this atom is not an integer
     */
    int toInt();
}
