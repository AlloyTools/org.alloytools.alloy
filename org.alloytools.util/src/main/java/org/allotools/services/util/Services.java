package org.allotools.services.util;

import java.util.ArrayList;
import java.util.List;
import java.util.ServiceLoader;

/**
 * Abstracts away the use of the service loader because I do not like how it is
 * tied to statics and classes. By abstracting it we can later insert other
 * mechanisms.
 */
public class Services {

	public static <S> List<S> getServices(Class<S> serviceType) {
		List<S> result = new ArrayList<>();
		for (S s : ServiceLoader.load(serviceType)) {
			result.add(s);
		}
		return result;
	}
}
