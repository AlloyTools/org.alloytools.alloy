package org.allotools.services.util;

import java.util.ArrayList;
import java.util.List;
import java.util.ServiceLoader;
import java.util.function.Function;

import org.alloytools.alloy.infrastructure.api.AlloyImplementation;
import org.alloytools.metainf.util.ManifestAccess;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import aQute.bnd.exceptions.Exceptions;
import aQute.libg.parameters.Attributes;
import aQute.libg.parameters.ParameterMap;

/**
 * Abstracts away the use of the service loader because I do not like how it is
 * tied to statics and classes. By abstracting it we can later insert other
 * mechanisms.
 */
public class Services {

    final static Logger logger = LoggerFactory.getLogger(Services.class);

    public static <S> List<S> getServices(Class<S> serviceType) {
        return getServices(serviceType, null);
    }

    public static <S, T extends S> List<S> getServices(Class<S> serviceType, Function<Class<T>,T> creator) {
        try {
            if (creator == null)
                creator = c -> {
                    try {
                        return c.newInstance();
                    } catch (Exception e1) {
                        e1.printStackTrace();
                        return null;
                    }
                };

            ClassLoader classLoader = serviceType.getClassLoader();
            List<S> result = new ArrayList<>();
            String name = serviceType.getCanonicalName();
            ParameterMap provides = ManifestAccess.getParameterHeader("Provide-Capability");
            for (Attributes attrs : provides.values()) {
                String interf = attrs.get(AlloyImplementation.INTERFACE);
                if (!name.equals(interf))
                    continue;

                String implementation = attrs.get(AlloyImplementation.IMPLEMENTATION);
                if (implementation == null) {
                    logger.error("alloy.ext capability does not contain implementation attr {}", attrs);
                    continue;
                }

                try {
                    @SuppressWarnings("unchecked" )
                    Class<T> type = (Class<T>) classLoader.loadClass(implementation);
                    T instance = creator.apply(type);
                    result.add(instance);
                } catch (Exception e) {
                    logger.error("alloy.ext capability, cannot find implementation {} {}", attrs, e, e);
                    continue;
                }
            }
            for (S s : ServiceLoader.load(serviceType, classLoader)) {
                result.add(s);
            }
            return result;
        } catch (Exception e) {
            throw Exceptions.duck(e);
        }
    }

    public static <S> S getService(Class<S> class1, Function<Class<S>,S> creator) {
        return getServices(class1, creator).get(0);
    }

    public static <S> S getService(Class<S> class1) {
        return getServices(class1, null).get(0);
    }
}
