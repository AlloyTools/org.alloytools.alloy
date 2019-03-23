package org.alloytools.alloy.core.api;

/**
 * Represents a value assignment that satisfies an Alloy specification. An
 * instance belongs to a {@link Solution}. A solution can have multiple
 * instances, all satisfying the same Alloy specification.
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
     * @param expr the expression to evaluate
     * @return the return value
     */
    IRelation eval(String expr);

    /**
     * Get the universe for this instance (i.e., all the atoms as a unary
     * relation)
     * 
     * @return the universe
     */
    IRelation universe();

    /**
     * Return the identity relation for this instance (i.e., a binary relation
     * where each atom is mapped to itself)
     * 
     * @return the identity relation
     */
    IRelation ident();
}
