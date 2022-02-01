package org.alloytools.alloy.core.api;

import java.util.List;

/**
 * A Field in a sig
 */
public interface TField {

    /**
     * The types of this field.
     *
     * @return the types of this relation
     */
    List<TSig> getType();

    /**
     * Parent type TODO (not sure this is needed?)
     *
     * @return the parent type
     */
    TSig getParent();

    /**
     * The name of the field
     */
    String getName();

    /**
     * Answer true if this field is a variable.
     */
    boolean isVariable();
}
