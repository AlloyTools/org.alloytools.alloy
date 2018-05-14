package org.allotools.conversion.util;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.lang.reflect.Type;
import java.util.LinkedHashMap;
import java.util.Map;

import aQute.lib.converter.Converter;

public class DTOs {

	@SuppressWarnings("unchecked")
	public static <T> T copy(T from, T to) {

		Class<? extends Object> class1 = from.getClass();
		assert class1 == to.getClass();

		if (to == null) {
			try {
				to = (T) class1.newInstance();
			} catch (Exception e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}

		for (java.lang.reflect.Field toField : to.getClass().getFields()) {
			try {
				java.lang.reflect.Field fromField = class1.getField(toField.getName());
				Object fromValue = fromField.get(from);
				Object toValue = convert(toField.getGenericType(), fromValue);
				toField.set(to, toValue);
			} catch (Exception e) {
				//
			}
		}
		return to;
	}

	@SuppressWarnings("unchecked")
	public static <T> T convert(Type type, Object source) {
		try {
			Object cnv = Converter.cnv(type, source);
			return (T) cnv;
		} catch (Exception e) {
			// TODO
			e.printStackTrace();
			throw new RuntimeException(e);
		}
	}

	@SuppressWarnings("unchecked")
	public static <T> T newInstance(T options) {
		return newInstance((Class<T>) options.getClass());
	}

	public static <T> T newInstance(Class<T> type) {
		try {
			return type.newInstance();
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
			throw new IllegalArgumentException(type + " not suitable to instantiate", e);
		}
	}

	public static <T> T m2i(Class<T> interfc, Map<String, Object> map) {
		if (map == null)
			map = new LinkedHashMap<String, Object>();
		return convert(interfc, map);
	}

	public static <T> T dflt(Class<T> class1) {
		return m2i(class1, null);
	}

	public static void set(Object options, Map<String, String> sourceOptions) {
		for (Field field : options.getClass().getFields()) {
			try {
				if (Modifier.isStatic(field.getModifiers()))
					continue;

				String string = sourceOptions.get(field.getName());
				if (string != null) {
					Object value = convert(field.getGenericType(), string);
					field.set(options, value);
				}
			} catch (Exception e) {
				// TODO log
				e.printStackTrace();
			}
		}
	}

	public static String readableTime(long l) {
		if (l < 1000) {
			return l + " ms";
		}
		l = (l + 500) / 1000;
		if (l < 60) {
			return l + " s";
		}

		l = (l + 30) / 60;
		if (l < 60) {
			return l + " min";
		}

		l = (l + 30) / 60;
		return l + " h";
	}

}
