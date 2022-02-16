package org.alloytools.alloy.core.api;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.SortedSet;


/**
 * A relation is a list of {@link ITuple}s. The {@link #arity()} is the arity
 * (length) of each tuple in this relation (all tuples in a relation must have
 * the same arity) and the {@link #size()} is the number of tuples in this
 * relation. A relation always belongs to a {@link Solution}.
 */
public interface IRelation extends Iterable<ITuple> {

    /**
     * The solution this relation belongs to
     *
     * @return the alloy solution this relation belongs to
     */
    Solution getSolution();

    /**
     * The arity of this relation (which must coincide with the arity of each tuple
     * in this relation)
     *
     * @return the arity
     */
    public int arity();

    /**
     * The number of tuples in this relation
     *
     * @return the number of tuples
     */
    int size();

    /**
     * Join this relation with another one
     *
     * @param right the relation to join with
     * @return the result of the join
     */
    IRelation join(IRelation right);

    /**
     * Join this relation with another one
     *
     * @param right the relation to join with
     * @return the result of the join
     */
    IRelation select(IAtom right);

    /**
     * Create a relation product of this relation and another one
     *
     * @param right the relation to create a product with
     * @return the result of the product
     */
    IRelation product(IRelation right);

    /**
     * Returns a new unary relation that contains only the 1st column (at index 0)
     * of this relation.
     *
     * @return the head of this relation
     */
    IRelation head();

    /**
     * Returns a new relation that contains all the columns of this relation but the
     * first.
     *
     * @return the tail of this relation
     */
    IRelation tail();

    /**
     * A relation is a "scalar" if it contains a single tuple with a single atom in
     * it (i.e., both the arity and the size of the relation is 1).
     *
     * @return is this tuple set a scalar?
     */
    default boolean isScalar() {
        return arity() == 1 && size() == 1;
    }

    /**
     * Is this relation empty (i.e., it contains 0 tuples)?
     *
     * @return whether this relation is empty.
     */
    default boolean isEmpty() {
        return size() == 0;
    }

    /**
     * Is this relation unary (i.e., its arity is 1)?
     *
     * @return whether this is a unary relation.
     */
    default boolean isUnary() {
        return arity() == 1;
    }

    /**
     * If this tuple sets holds a single scalar then this method returns the scalar.
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
     * Return the most left column as a list of atoms PRECONDITION: this must be a
     * unary relation
     *
     * @return a list of atoms
     */
    default List<IAtom> asList() {
        assert isUnary();

        List<IAtom> list = new ArrayList<>();

        for (ITuple tuple : this) {
            list.add(tuple.get(0));
        }

        return list;
    }

    /**
     * See {@link #equals(Object)}
     *
     * @return a hash code
     */
    @Override
    int hashCode();

    /**
     * Two relations are equal when they have the same arity, the same size, and the
     * same sets of tuples.
     *
     * @return true if equal to {@code o}
     */
    @Override
    boolean equals(Object o);

    /**
     * Answer true if all our tuples appear in the other relation. If the arity
     * differs, this will return false.
     *
     * @param other the other relation.
     */
    boolean in(IRelation other);

    /**
     * Answer true if we contain this tuple.
     *
     * @param tuple the tuple to check
     */
    boolean contains(ITuple tuple);

    /**
     * Answer the difference between this set and the other set.
     *
     * <pre>
     *  this'  = this - other
     * </pre>
     *
     * @param other the relation that will be subtracted from this
     */
    IRelation difference(IRelation atoms);

    /**
     * Answer the union between this set and the other set.
     *
     * <pre>
     *  this'  = this + other
     * </pre>
     *
     * @param other the relation that will be subtracted from this
     */
    IRelation union(IRelation other);

    /**
     * Answer the intersection between this set and the other set.
     *
     * <pre>
     *  this'  = this & other
     * </pre>
     *
     * @param other the relation that will be subtracted from this
     */
    IRelation intersection(IRelation other);


    /**
     * Answer the set of tuples.
     */
    SortedSet<ITuple> asSet();

    default int toInt() {
        return scalar().map(a -> a.toInt()).orElseThrow(IllegalArgumentException::new);
    }
}
