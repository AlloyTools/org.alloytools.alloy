package org.alloytools.alloy.dto;

import java.util.ArrayList;
import java.util.List;

/**
 * Represents an open instruction.
 */
public class OpenDTO {

    /**
     * The module addressed
     */
    public ModuleDTO    module;

    /**
     * The parameters specified in the open instruction
     */
    public List<String> parameters = new ArrayList<>();
}
