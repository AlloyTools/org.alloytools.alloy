package org.alloytools.alloy.core.api;

import java.util.Collections;
import java.util.List;

public interface TExpression {

    TType getType();

    Position getPosition();

    default List<TExpression> getChildren() {
        return Collections.emptyList();
    }
}
