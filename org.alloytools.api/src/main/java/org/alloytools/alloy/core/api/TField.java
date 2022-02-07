package org.alloytools.alloy.core.api;

/**
 * A Field in a sig
 */
public interface TField {

    /**
     * The expression for the definition of this field.
     *
     * @return the types of this relation
     */
    TExpression getExpression();

    /**
     * Parent type TODO (not sure this is needed?)
     *
     * @return the parent type
     */
    TSignature getParent();

    /**
     * The name of the field
     */
    String getName();

    /**
     * Answer true if this field is a variable.
     */
    boolean isVariable();
}
