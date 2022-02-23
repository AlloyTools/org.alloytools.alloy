package org.alloytools.alloy.core.api;

import java.util.Set;

interface TDeclaration {

    /**
     * The name of the field
     */
    String getName();

    /**
     * The expression for the definition of this field. <br/>
     * TODO figure out the type, is it the Power type or the set to chose from
     *
     * @return the types of this relation
     */
    TExpression getExpression();


    /**
     * Disjunct set of names.
     */

    Set<String> getDisjunct();
}

