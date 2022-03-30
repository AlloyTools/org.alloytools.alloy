package org.alloytools.alloy.infrastructure.api;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

import org.osgi.annotation.bundle.Attribute;
import org.osgi.annotation.bundle.Capability;

@Capability(
            namespace = AlloyImplementation.NAMESPACE,
            attribute = {

                         AlloyImplementation.IMPLEMENTATION + "=${@class}", "interface=org.alloytools.alloy.core.api.Visualizer"
            } )
@Target(ElementType.TYPE )
@Retention(RetentionPolicy.RUNTIME )
public @interface AlloyVisualizer {

    @Attribute
    String name();
}
