package org.alloytools.alloy.dto;


/**
 * A Data Transfer Object (DTO) that encapsulates information about a specific
 * field within an Alloy signature.
 *
 */
public class FieldDTO {

    /**
     * The unique identifier or label of the field. This property captures the name
     * of the field as it is defined within the Alloy signature.
     */
    public String  name;

    /**
     * Specifies whether the field is a meta field within the Alloy signature. Meta
     * fields are describing the structure of the sig and fields.
     */
    public boolean meta;

    /**
     * Specifies whether the field is defined as a variable within the Alloy
     * signature. Variable fields generally represent dynamic values that can change
     * during execution.
     */
    public boolean var;

    /**
     * Represents the data type of the field as defined within the Alloy signature.
     * This property provides information about the kind of values the field can
     * hold or represent.
     */
    public String  type;

    public int     arity;

}
