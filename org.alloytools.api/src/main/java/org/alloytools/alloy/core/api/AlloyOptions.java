package org.alloytools.alloy.core.api;

import java.lang.reflect.Type;
import java.util.Map;

/**
 * Wrapper around a DTO for options. In Alloy, parties that need options should
 * define this as a DTO. A DTO is of a public class with public fields of the
 * simple types (primitives, String, Number, Enum, Collections, Map, and DTO)
 *
 * @param <X> the DTO type
 */
public interface AlloyOptions<X> extends Iterable<String> {

    /**
     * Used to create a type reference
     *
     * @param <F>
     */
    class TypeRef<F> {
    }

    Object get(String name);

    <T> T get(String name, Class<T> type);

    <T> T set(String name, T value);

    Type type(String name);

    default void on(String name) {
        set(name, true);
    }

    default void off(String name) {
        set(name, false);
    }

    X get();

    Object get(String name, Type type);

    <Z> Z get(String name, TypeRef<Z> type);

    void set(Map<String, ? > value);
}
