package org.alloytools.alloy.infrastructure.api;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

import org.osgi.annotation.bundle.Capability;

@Capability(
            namespace = AlloyImplementation.NAMESPACE,
            attribute = {
                         AlloyImplementation.IMPLEMENTATION + "=${@class}", "interface=org.alloytools.cli.api.CLICommand"
            } )
@Target(ElementType.TYPE )
@Retention(RetentionPolicy.RUNTIME )
public @interface AlloyCLI {

    String[] subCommand();

    boolean isDefault() default false;
}
