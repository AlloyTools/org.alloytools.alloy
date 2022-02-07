package org.alloytools.alloy.core.api;

import java.util.Collections;
import java.util.List;

public interface TExpression {

    List<TSignature> getType();

    Position getPosition();

    default List<TExpression> getChildren() {
        return Collections.emptyList();
    }
}
