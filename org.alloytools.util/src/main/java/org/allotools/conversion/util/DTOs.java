package org.allotools.conversion.util;

import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.lang.reflect.Type;
import java.util.LinkedHashMap;
import java.util.Map;

import aQute.lib.converter.Converter;

public class DTOs {

    @SuppressWarnings("unchecked" )
    public static <T> T copy(T from, T to) {
        try {
            Class< ? extends Object> class1 = from.getClass();
            assert class1 == to.getClass();

            if (to == null) {
                to = (T) class1.newInstance();
            }

            for (java.lang.reflect.Field toField : to.getClass().getFields()) {
                java.lang.reflect.Field fromField = class1.getField(toField.getName());
                Object fromValue = fromField.get(from);
                Object toValue = convert(toField.getGenericType(), fromValue);
                toField.set(to, toValue);
            }
            return to;
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }

    @SuppressWarnings("unchecked" )
    public static <T> T convert(Type type, Object source) {
        try {
            Object cnv = Converter.cnv(type, source);
            return (T) cnv;
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }

    @SuppressWarnings("unchecked" )
    public static <T> T newInstance(T options) {
        return newInstance((Class<T>) options.getClass());
    }

    public static <T> T newInstance(Class<T> type) {
        try {
            return type.newInstance();
        } catch (Exception e) {
            throw new IllegalArgumentException(type + " not suitable to instantiate", e);
        }
    }

    public static <T> T m2i(Class<T> interfc, Map<String,Object> map) {
        if (map == null)
            map = new LinkedHashMap<>();
        return convert(interfc, map);
    }

    public static <T> T dflt(Class<T> class1) {
        return m2i(class1, null);
    }

    public static void set(Object options, Map<String,String> sourceOptions) {
        try {
            for (Field field : options.getClass().getFields()) {
                if (Modifier.isStatic(field.getModifiers()))
                    continue;

                String string = sourceOptions.get(field.getName());
                if (string != null) {
                    Object value = convert(field.getGenericType(), string);
                    field.set(options, value);
                }
            }
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }

    public static void copyDTOToBean(Object dto, Object bean) {

        for (Field f : dto.getClass().getFields()) {
            if (Modifier.isStatic(f.getModifiers()))
                continue;

            String name = f.getName();
            String setName = toSet(name);

            try {

                Method method = bean.getClass().getMethod(setName, f.getType());
                method.invoke(bean, f.get(dto));

            } catch (NoSuchMethodException e) {
                // ignore, not al options are in kodkod
            } catch (Exception e) {
                throw new RuntimeException(e);
            }
        }


    }

    static String toSet(String name) {
        StringBuilder sb = new StringBuilder();
        sb.append("set");
        char c = name.charAt(0);
        sb.append(Character.toUpperCase(c));
        sb.append(name.substring(1));
        return sb.toString();
    }



    public static String readableTime(long timeMs) {
        if (timeMs < 1000) {
            return timeMs + " ms";
        }

        timeMs = (timeMs + 500) / 1000;
        if (timeMs < 60) {
            return timeMs + " s";
        }

        timeMs = (timeMs + 30) / 60;
        if (timeMs < 60) {
            return timeMs + " min";
        }

        timeMs = (timeMs + 30) / 60;
        return timeMs + " h";
    }

}
