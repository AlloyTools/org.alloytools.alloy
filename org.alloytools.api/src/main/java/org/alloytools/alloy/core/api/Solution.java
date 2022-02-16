package org.alloytools.alloy.core.api;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Spliterator;
import java.util.Spliterators;
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
     * variables are varied. See {@link #trace(Instance)}
     *
     * @return true if the underlying model has variables.
     */
    boolean hasVariables();


    /**
     * Return an iterator over the instances. Each instance is a configuration
     * instance, i.e. only the static parts are resolved. Since resolving is
     * expensive in time, the solutions should be fetched when needed and not
     * earlier. The actual resultion generally takes place when calling
     * {@link Iterator#hasNext()}.
     *
     * @return An iterator over the configuration instances.
     */
    Iterator<Instance> iterator();

    default Stream<Instance> stream() {
        Spliterator<Instance> spliterator = Spliterators.spliteratorUnknownSize(iterator(), 0);
        return StreamSupport.stream(spliterator, false);
    }

    /**
     * Each configuration instance is associated with a Trace. A Trace is the graph
     * of instances where the last instance loops back to an earlier instance to
     * mimic an inifite trace.
     * <p>
     * This method creates a new Trace from a <em>current</em> Instance. An instance
     * can be a <em>configuration Instance</em> or a member of a Trace. It is
     * possible to iterate over all the traces associated with a configuration
     * instance , or over traces that share ancestor instances.
     * <p>
     * If the current Instance is a configuration INstance, then a Trace iterator
     * based on that configuration only return.
     * <p>
     * If current is a instance from a trace, the returned trace will share the same
     * ancestors as the current instance.
     *
     * @param current instance, either a configuration (a.k.a. init) or a trace
     *            instance (a.k.a. fork)
     * @return an iterator over the traces of the current instance
     */
    Iterable<Trace> trace(Instance current);

    /**
     * Represents a trace. A trace is a set of instances over time. The last
     * instance loops back to an earlier instance.
     */
    interface Trace {

        /**
         * The sequence of instances
         */
        Instance[] instances();

        /**
         * Normally the instances are ordered by the array index. However, the last
         * instance loops back to the index returned here.
         *
         * <pre>
         * loop >=0 and loop < #instances
         * </pre>
         */
        int loop();
    }

    default Instance[] next(int max) {
        List<Instance> l = new ArrayList<>();
        for (Instance instance : this) {
            l.add(instance);
            if (l.size() >= max)
                break;
        }

        return l.toArray(new Instance[l.size()]);
    }

    TSignature bool();

}
