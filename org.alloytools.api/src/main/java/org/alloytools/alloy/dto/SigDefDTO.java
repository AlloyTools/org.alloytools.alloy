package org.alloytools.alloy.dto;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * A Data Transfer Object (DTO) that encapsulates information about a specific
 * Alloy signature definition.
 *
 * This class provides an organized and structured method to transfer data
 * regarding a specific Alloy signature.
 */
public class SigDefDTO {

    /**
     * The unique identifier or label of the signature definition. This property
     * captures the name of the signature as it is defined within the Alloy model.
     * It includes the module name or `this` if it is the root model.
     */
    public String               name;

    /**
     * Specifies the cardinality of the signature definition. The cardinality
     * property determines the number of instances that can be associated with the
     * signature.
     */
    public Cardinality          cardinality;

    /**
     * Specifies whether the signature definition is an enumeration. Enumerations
     * typically represent a type with a predefined set of constant values.
     */
    public boolean              isEnum;

    /**
     * Specifies whether the signature definition is a meta signature. Meta
     * signatures are typically used to add additional context or metadata about the
     * model.
     */
    public boolean              meta;

    /**
     * Specifies whether the signature definition is a built-in type. Built-in types
     * are provided by the Alloy language itself, such as integers or strings.
     */
    public boolean              builtin;

    /**
     * Represents the data type of the signature definition. This property provides
     * information about the type that the signature represents within the Alloy
     * model.
     */
    public String               type;

    /**
     * A list of FieldDTO objects that represent the fields associated with this
     * signature. Each FieldDTO object within this list encapsulates information
     * about a specific field within the signature.
     */
    public Map<String,FieldDTO> fields = new LinkedHashMap<>();
}
