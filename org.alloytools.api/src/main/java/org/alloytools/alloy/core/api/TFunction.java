package org.alloytools.alloy.core.api;

import java.util.List;

public interface TFunction {

    String getName();

    List<TParameter> getParameters();

    boolean isPredicate();

    TExpression call(TExpression... args);
}
