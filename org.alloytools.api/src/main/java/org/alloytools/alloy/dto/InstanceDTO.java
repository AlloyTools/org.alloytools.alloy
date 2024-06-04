package org.alloytools.alloy.dto;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

/**
 * A Data Transfer Object (DTO) representing a specific instance within an Alloy
 * solution.
 *
 * This class provides a structured way to encapsulate and transfer data related
 * to a particular instance in an Alloy solution.
 */
public class InstanceDTO {

    /**
     * An instance contains relations. Each field has a relation and there are a
     * number of skolem variables that have a relation. sig -> field -> tuples...
     */
    public Map<String,Map<String,String[][]>> values   = new TreeMap<>();

    /**
     * A mapping of Skolem functions within this instance. Each key is a Skolem
     * function name, and its associated value is an object representing the value
     * or values produced by that function.
     */
    public Map<String,TuplesDTO>              skolems  = new TreeMap<>();

    /**
     * If part of a temporal solution, the index in the trace. Otherwise -1
     */
    public int                                state;

    public List<String>                       messages = new ArrayList<>();
}
