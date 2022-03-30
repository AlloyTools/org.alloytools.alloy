package org.alloytools.alloy.core.api;

import java.util.List;

public interface TFunction {

    /**
     * The local name of the function
     */
    String getName();

    /**
     * The list of formal parameters
     */
    List<TParameter> getParameters();

    /**
     * If this is a predicate
     */
    boolean isPredicate();

    /**
     * Call this function with the given values
     *
     * @param args the list of arguments
     */
    TExpression call(TExpression... args);
}
