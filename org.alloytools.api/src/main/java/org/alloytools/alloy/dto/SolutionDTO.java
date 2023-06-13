package org.alloytools.alloy.dto;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * A Data Transfer Object (DTO) representing a specific Alloy solution.
 *
 * This class provides a structured way to encapsulate and transfer data related
 * to a particular solution generated from an Alloy model.
 */
public class SolutionDTO {

    /**
     * Indicates whether the solution is satisfiable, i.e., whether a valid instance
     * of the model exists that satisfies all constraints.
     */
    public boolean               satisfiable;


    /**
     * A list of InstanceDTO objects that represent the instances associated with
     * this solution. Each InstanceDTO object within this list encapsulates
     * information about a specific instance within the solution.
     */
    public List<InstanceDTO>     instances = new ArrayList<>();

    /**
     * The index of the instance that is the final loopback. All traces run to the
     * last instance and then continue to the loop state. If the solution is not
     * dynamic or not satisfied, the loop state is -1.
     */
    public int                   loopstate = -1;

    /**
     * The name of the solver
     */
    public String                solver;

    /**
     * The time, in milliseconds since the Unix epoch, at which the solution was
     * generated.
     */
    public long                  utctime;

    /**
     * The command or operation that generated this solution.
     */
    public String                command;


    /**
     * Indicates whether the solution was obtained incrementally. Incremental
     * solutions can be useful for solving complex problems piece by piece.
     */
    public boolean               incremental;

    public String                localtime;

    public ModuleDTO             module;

    /**
     * The name of the Alloy module from which this solution was derived.
     */
    public ModuleDTO             root;
    /**
     * The bit width used for integers in this solution. Bit width is used to limit
     * the range of integer values that can be represented.
     */
    public int                   bitwidth;

    /**
     * The number of recursive unrollings performed during the generation of this
     * solution.
     */
    public int                   unrolls;

    /**
     * Overflow is allowed
     */
    public boolean               overflow;

    /**
     * Skolem depth
     */
    public int                   skolemDepth;

    /**
     * A list of SigDefDTO objects that represent the signatures associated with
     * this solution. Each SigDefDTO object within this list encapsulates
     * information about a specific signature within the solution.
     */
    public Map<String,SigDefDTO> sigs      = new LinkedHashMap<>();


}
