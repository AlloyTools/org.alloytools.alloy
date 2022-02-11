package org.alloytools.alloy.core.api;

/**
 * A warning or error from the compilation
 */
public interface CompilerMessage {

    /**
     * The actual message
     *
     * @return the messsage
     */
    String getMessage();

    /**
     * The total source code of the module
     *
     * @return the source code
     */
    String getSource();

    Position getPosition();
}
