package org.alloytools.alloy.dto;


/**
 * Represents a Tuple set.
 */
public class TuplesDTO {

    /**
     * The arity of the tuple set. This should match the associated type even if
     * empty
     */
    public int        arity;

    /**
     * The array of tuples.
     */
    public String[][] data;
}
