package org.alloytools.alloy.core.api;

import java.util.Optional;

/**
 * Represents a value assignment that satisfies an Alloy specification. An
 * instance belongs to a {@link Solution}. A solution can have multiple
 * instances, all satisfying the same Alloy specification.
 * <p>
 * An instance represents the <em>state</em> of a model. Each satisfied
 * {@link Solution} provides a set of {@link Instance} objects where the static
 * aspects of the model can vary.
 * <p>
 * If a model has variables, then the instance represents the root of a time
 * <em>trace</em>. A trace is a set of instances representing a possible state
 * of the model in time. The API provides methods to navigate through the static
 * state of the model (a.k.a. configurations) and the state of the variables of
 * the model (a.k.a. traces).
 *
 */
public interface Instance {

    /**
     * Get the value of a field
     *
     * @param field the field
     * @return the values
     */
    IRelation getField(TField field);

    /**
     * Get the valueof a sig.
     *
     * @param sig the sig
     * @return the atoms with an arity=1
     */
    IRelation getAtoms(TSig sig);

    /**
     * Get the value of a variable from a function.
     *
     * @param functionName the function name
     * @param varName the variable name
     * @return the value (can be empty)
     */
    IRelation getVariable(String functionName, String varName);

    /**
     * Evaluate an expression in the context of this instance. TODO what is the
     * syntax?
     *
     * @param expr the expression to evaluate.
     * @return the return value. This is either a Boolean or a IRelation
     */
    Object eval(String expr);

    /**
     * Get the universe for this instance (i.e., all the atoms as a unary relation)
     *
     * @return the universe
     */
    IRelation universe();

    /**
     * Return the identity relation for this instance (i.e., a binary relation where
     * each atom is mapped to itself)
     *
     * @return the identity relation
     */
    IRelation ident();

    /**
     * Returns another Instance that has the same state ancestors as this instance
     * but will be a different trace then the current trace. I.e. the new trace will
     * traverse a different set of Instance objects.
     * <p>
     * A instance can point back to an earlier instance but repeatedly calling fork
     * will end in the return of an empty.
     * <p>
     * If the instance has no variables this will always return empty.
     * <p>
     * This call is idempotent.
     *
     * @return a new Instance or empty if no new trace exists.
     */
    Optional<Instance> fork();

    /**
     * Return an Instance that has the same configuration as this Instance but
     * represents a different trace. If no new trace can be found, it will return an
     * empty.
     * <p>
     * If the instance has no variables this will always return empty.
     * <p>
     * This call is idempotent.
     *
     * @return a
     */
    Optional<Instance> init();

    /**
     * Return an Instance that has a different configuration as this Instance. If no
     * new instance could be found, this returns empty.
     * <p>
     * This call is idempotent.
     *
     * @return a
     */
    Optional<Instance> config();

    /**
     * Return the parent of this instance. The first instance will return for the
     * parent.
     * <p>
     * This call is idempotent.
     */

    Optional<Instance> parent();
}
