package org.alloytools.alloy.infrastructure.api;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

import org.osgi.annotation.bundle.Capability;

@Capability(
            namespace = AlloySolver.NAMESPACE,
            attribute = {
                         AlloySolver.FQN + "=${@class}"
            } )
@Target(ElementType.TYPE )
@Retention(RetentionPolicy.RUNTIME )
public @interface AlloySolver {

    String NAMESPACE = "alloy.solver";
    String FQN       = "type";
}
