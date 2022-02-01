package org.alloytools.alloy.core.api;

import java.util.stream.Stream;
import java.util.stream.StreamSupport;

/**
 * A solution is produced by a {@link Solver}. It can either be satisfiable or
 * not. Only a satisfiable solution contains instances.
 */
public interface Solution extends Iterable<Instance> {

    /**
     * The solver that produced this solution
     *
     * @return the solver that produced this solution
     */
    Solver getSolver();

    /**
     * The options used when solving for this solution
     *
     * @return the options used when solving for this solution
     */
    SolverOptions getOptions();

    /**
     * The module this solution was derived from.
     *
     * @return the module this solution was derived from.
     */
    Module getModule();

    /**
     * The command this is a solution to
     *
     * @return the command this is a solution to
     */
    TCommand getCommand();

    /**
     * Whether the specification was satisfiable or not.
     */
    boolean isSatisfied();

    /**
     * Returns an empty relation.
     *
     * @return an empty relation.
     */
    IRelation none();


    /**
     * Return true if the model that this solution was derived from had variables.
     * Models with variables can create <em>traces</em> where the values of the
     * variables are varied. This is reflected in the {@link Instance#fork()} and
     * {@link Instance#init()} methods.
     *
     * @return true if the underlying model has variables.
     */
    boolean hasVariables();


    /**
     * Turn this solution into a stream of instances.
     *
     * @return a stream of instances
     */
    default Stream<Instance> stream() {
        return StreamSupport.stream(this.spliterator(), false);
    }
}
