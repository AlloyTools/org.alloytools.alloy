package org.alloytools.alloy.infrastructure.api;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

import org.osgi.annotation.bundle.Capability;

/**
 *
 * @author aqute
 *
 */

@Capability(
            namespace = AlloyMain.NAMESPACE,
            attribute = {
                         AlloyMain.FQN + "=${@class}"
            } )
@Retention(RetentionPolicy.RUNTIME )
@Target(ElementType.TYPE )
public @interface AlloyMain {

    String NAMESPACE = "alloy.main";
    String FQN       = "fqn";
}
