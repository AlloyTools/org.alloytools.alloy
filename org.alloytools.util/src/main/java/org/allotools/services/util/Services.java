package org.allotools.services.util;

import java.util.ArrayList;
import java.util.List;
import java.util.ServiceLoader;

import org.alloytools.alloy.core.api.Alloy;

/**
 * Abstracts away the use of the service loader because I do not like how it is
 * tied to statics and classes. By abstracting it we can later insert other
 * mechanisms.
 */
public class Services {

    public static <S> List<S> getServices(Class<S> serviceType) {
        List<S> result = new ArrayList<>();
        for (S s : ServiceLoader.load(serviceType, serviceType.getClassLoader())) {
            result.add(s);
        }
        return result;
    }

    public static Alloy getService(Class<Alloy> class1) {
        return getServices(class1).get(0);
    }
}
