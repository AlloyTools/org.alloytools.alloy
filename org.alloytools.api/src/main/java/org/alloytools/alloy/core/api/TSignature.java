package org.alloytools.alloy.core.api;

import java.util.Map;
import java.util.Optional;

/**
 * Represents a signature in Alloy.
 */
public interface TSignature {

    /**
     * The name of the signature
     *
     * @return the name of the signature.
     */
    String getName();

    /**
     * The field relations associated with the signature
     *
     * @return the fields
     */
    Map<String,TField> getFieldMap();

    /**
     * Get a particular field
     *
     * @param fieldName the field name
     * @return an optional field
     */
    Optional<TField> getField(String fieldName);
}
