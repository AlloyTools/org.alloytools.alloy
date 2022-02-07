package org.alloytools.alloy.core.api;

import java.util.List;

public interface TFunction {

    interface Parameter {

        String getName();

        TExpression getType();
    }

    String getName();

    List<Parameter> getParameters();

    boolean isPredicate();

    TExpression call(TExpression... args);
}
