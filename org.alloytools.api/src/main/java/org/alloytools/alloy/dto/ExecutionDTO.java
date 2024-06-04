package org.alloytools.alloy.dto;

import java.util.LinkedHashMap;
import java.util.Map;

public class ExecutionDTO {

    public String                 solver;
    public long                   timestamp;
    public boolean                noOverflow;
    public int                    symmetry;
    public int                    unrolls;
    public int                    coreGranularity;
    public int                    coreMinimization;
    public boolean                inferPartialInstance;
    public int                    decompose_mode;
    public int                    skolemDepth;
    public int                    repeat;
    public Map<String,CommandDTO> commands = new LinkedHashMap<>();
    public Map<String,SigDefDTO>  sigs     = new LinkedHashMap<>();
}
