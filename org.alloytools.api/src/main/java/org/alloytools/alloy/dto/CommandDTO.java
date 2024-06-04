package org.alloytools.alloy.dto;

import java.util.ArrayList;
import java.util.List;

public class CommandDTO {

    public enum CommandType {
                             check,
                             run
    }

    public CommandType       type;
    public String            name;

    public String            scope;
    public String            source;
    public List<String>      scopes   = new ArrayList<>();
    public int               expects;
    public int               maxseq;
    public int               maxprefix;
    public int               minprefix;
    public int               overall;
    public String            transformPath;
    public List<SolutionDTO> solution = new ArrayList<>();
    /**
     * The name of the solver
     */
    public String            solver;
    /**
     * The command or operation that generated this solution.
     */
    public String            command;
    public ModuleDTO         module;

    /**
     * The name of the Alloy module from which this solution was derived.
     */
    public ModuleDTO         root;
    /**
     * The bit width used for integers in this solution. Bit width is used to limit
     * the range of integer values that can be represented.
     */
    public int               bitwidth;

    /**
     * The number of recursive unrollings performed during the generation of this
     * solution.
     */
    public int               unrolls;

    /**
     * Overflow is allowed
     */
    public boolean           overflow;

    /**
     * Skolem depth
     */
    public int               skolemDepth;


}
