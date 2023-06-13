package org.alloytools.alloy.dto;

import java.util.ArrayList;
import java.util.List;

/**
 * Represents a module
 */
public class ModuleDTO {

    /**
     * The name of the module or null
     */
    public String        name;
    /**
     * The open statements in order
     */
    public List<OpenDTO> opens = new ArrayList<>();

    /**
     * The file path
     */
    public String        path;
}
