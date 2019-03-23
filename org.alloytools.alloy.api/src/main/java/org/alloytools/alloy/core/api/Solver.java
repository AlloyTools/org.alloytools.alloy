package org.alloytools.alloy.core.api;

/**
 * Represents a solver.
 */
public interface Solver {

    /**
     * The identity of the solver. This identity must be unique world-wide so a
     * FQN is recommended. For example, the primary class name.
     * 
     * @return the identity
     */
    String getId();

    /**
     * Get a human readable name.
     * 
     * @return a name
     */
    String getName();

    /**
     * Some solvers use native code or remote access. This flag indicates if the
     * solver is available on the platform or not.
     * 
     * @return true if this solver can run on the platform
     */
    boolean isAvailable();

    /**
     * Get the {@link SolverType}
     * 
     * @return the solver type.
     */
    SolverType getSolverType();

    /**
     * Get a short English description of this solver.
     * 
     * @return a description
     */
    String getDescription();

    /**
     * Return a DTO that has public fields that can be set by the end user to
     * activate custom options in this solver.
     * 
     * @return a DTO with options
     */
    SolverOptions newOptions();

    /**
     * Solve a constraint problem embodied in an Alloy command.
     * 
     * @param command the command to run/check
     * @param options the specified options or null if not options are given
     * @param lowerBound provide the lower bound for the solution
     * @return a Solution
     */
    Solution solve(TCommand command, SolverOptions options, Instance lowerBound);
}
