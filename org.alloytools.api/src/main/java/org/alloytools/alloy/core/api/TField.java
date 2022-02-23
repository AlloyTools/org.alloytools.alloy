package org.alloytools.alloy.core.api;

/**
 * A Field in a sig
 */
public interface TField extends TDeclaration {

    /**
     * Parent type TODO (not sure this is needed?)
     *
     * @return the parent type
     */
    TSignature getParent();

    /**
     * Answer true if this field is a variable.
     */
    boolean isVariable();
}
