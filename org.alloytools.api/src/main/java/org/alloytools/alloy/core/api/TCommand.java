
package org.alloytools.alloy.core.api;

import java.util.Set;

public interface TCommand {

    enum Expects {
                  UNKNOWN,
                  SATISFIABLE,
                  UNSATISFIABLE
    }

    /**
     * The name of the command
     */
    String getName();

    /**
     * Return the scopes defined by this command
     *
     * @return scopes defined by this command
     */
    Set<TScope> getScopes();

    /**
     * A hint whether the command is expected to be satisfiable or not. This is
     * mainly used for testing and documentation purposes and has no effect on
     * solving.
     *
     * @return expects
     */
    Expects getExpects();

    /**
     * Get the associated module.
     *
     * @return the module
     */
    Module getModule();

    TExpression getExpression();

    boolean isCheck();
}
