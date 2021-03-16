/*
 * Kodkod -- Copyright (c) 2005-2008, Emina Torlak
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */
package tests.util;

import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import kodkod.ast.Formula;
import kodkod.engine.fol2sat.TranslationLog;
import kodkod.engine.satlab.ReductionStrategy;
import kodkod.instance.Bounds;

/**
 * Provides a collection of utility methods for finding and executing benchmark
 * methods and constructors reflectively.
 *
 * @author Emina Torlak
 */
public final class Reflection {

    private Reflection() {}

    /**
     * This method invokes each method in the given set on the given instance, and
     * returns a map from the invoked methods to the resulting objects.
     *
     * @return a map from the given methods to the objects they produced when
     *         invoked on the given instance.
     */
    @SuppressWarnings("unchecked" )
    public static <T> Map<Method,T> invokeAll(Object instance, Set<Method> methods) {
        final Map<Method,T> ret = new LinkedHashMap<Method,T>();
        for (Method m : methods) {
            try {
                ret.put(m, (T) m.invoke(instance));
            } catch (IllegalArgumentException e) {} catch (IllegalAccessException e) {} catch (InvocationTargetException e) {}
        }
        return ret;
    }

    /**
     * Returns all public member methods declared by the given class that take no
     * arguments, return a Formula, and whose name starts with the word "check".
     *
     * @return all public member methods declared by the given class that take no
     *         arguments, return a Formula, and whose name starts with the word
     *         "check".
     */
    public static Set<Method> checks(Class< ? > c) {
        final Set<Method> methods = new LinkedHashSet<Method>();
        for (Method m : c.getMethods()) {
            if (m.getDeclaringClass().equals(c) && m.getName().startsWith("check") && noArgs(m) && returnsFormula(m)) {
                methods.add(m);
            }
        }
        return methods;
    }

    /**
     * Returns the public member method with the given name and no arguments that
     * returns a formula.
     *
     * @return public member method with the given name and no arguments that
     *         returns a formula.
     **/
    public static Method formulaCreator(Class< ? > c, String name) {
        try {
            Method m = c.getMethod(name, new Class[0]);
            if (returnsFormula(m))
                return m;
            else {
                throw new IllegalArgumentException("Wrong signature for method " + name + ".");
            }
        } catch (SecurityException e) {
            throw new IllegalArgumentException("Cannot access method " + name + ".");
        } catch (NoSuchMethodException e) {
            throw new IllegalArgumentException("Method " + name + " does not exist.");
        }

    }

    /**
     * Returns the bounds for the given instance. This method assumes that the
     * instance has a no-argument method called "bounds" that returns a Bounds
     * object.
     *
     * @requires instance must have a method called bounds that takes no arguments
     *           and returns a Bounds object
     * @return instance.bounds()
     */
    public static Bounds bounds(Object instance) {
        try {
            final Method bounder = instance.getClass().getMethod("bounds", new Class[] {});
            return (Bounds) bounder.invoke(instance);
        } catch (SecurityException e) {
            throw new IllegalArgumentException(instance.getClass().getName() + " has no accessible Bounds bounds(int) method.");
        } catch (NoSuchMethodException e) {
            throw new IllegalArgumentException(instance.getClass().getName() + " has no Bounds bounds(int) method.");
        } catch (IllegalAccessException e) {
            throw new IllegalArgumentException("Could not invoke Bounds bounds(int) method of " + instance.getClass().getName() + ".");
        } catch (InvocationTargetException e) {
            throw new IllegalArgumentException("Could not invoke Bounds bounds(int) method of " + instance.getClass().getName() + ".");
        }
    }

    /**
     * Returns the bounds for the given instance. This method assumes that the
     * instance has a method called "bounds" that takes a single integer argument
     * and returns a Bounds object.
     *
     * @requires instance must have a method called bounds that takes an integer
     *           argument and returns a Bounds object
     * @return instance.bounds(scope)
     */
    public static Bounds bounds(Object instance, int scope) {
        try {
            final Method bounder = instance.getClass().getMethod("bounds", new Class[] {
                                                                                        int.class
            });
            return (Bounds) bounder.invoke(instance, scope);
        } catch (SecurityException e) {
            throw new IllegalArgumentException(instance.getClass().getName() + " has no accessible Bounds bounds(int) method.");
        } catch (NoSuchMethodException e) {
            throw new IllegalArgumentException(instance.getClass().getName() + " has no Bounds bounds(int) method.");
        } catch (IllegalAccessException e) {
            throw new IllegalArgumentException("Could not invoke Bounds bounds(int) method of " + instance.getClass().getName() + ".");
        } catch (InvocationTargetException e) {
            throw new IllegalArgumentException("Could not invoke Bounds bounds(int) method of " + instance.getClass().getName() + ".");
        }
    }

    /**
     * Returns an instance of the given reduction strategy.
     *
     * @requires strategy has a constructor that takes a translation log
     * @return an instance of the given reduction strategy.
     */
    public static ReductionStrategy strategy(Class< ? extends ReductionStrategy> strategy, TranslationLog log) {
        try {
            return strategy.getConstructor(TranslationLog.class).newInstance(log);
        } catch (IllegalArgumentException e) {
            throw e;
        } catch (SecurityException e) {
            throw new IllegalArgumentException(strategy.getName() + " has no accessible one-argument constructor.");
        } catch (InstantiationException e) {
            throw new IllegalArgumentException(strategy.getName() + " has no accessible one-argument constructor.");
        } catch (IllegalAccessException e) {
            throw new IllegalArgumentException(strategy.getName() + " has no accessible one-argument constructor.");
        } catch (InvocationTargetException e) {
            throw new IllegalArgumentException(strategy.getName() + " has no accessible one-argument constructor.");
        } catch (NoSuchMethodException e) {
            throw new IllegalArgumentException(strategy.getName() + " has no accessible one-argument constructor.");
        }
    }

    /**
     * Returns an instance of the given reduction strategy.
     *
     * @requires strategy has a constructor that takes a translation log and an
     *           integer
     * @return an instance of the given reduction strategy.
     */
    public static ReductionStrategy strategy(Class< ? extends ReductionStrategy> strategy, TranslationLog log, int depth) {
        try {
            return strategy.getConstructor(TranslationLog.class, int.class).newInstance(log, depth);
        } catch (IllegalArgumentException e) {
            throw e;
        } catch (SecurityException e) {
            throw new IllegalArgumentException(strategy.getName() + " has no accessible two-argument constructor.");
        } catch (InstantiationException e) {
            throw new IllegalArgumentException(strategy.getName() + " has no accessible two-argument constructor.");
        } catch (IllegalAccessException e) {
            throw new IllegalArgumentException(strategy.getName() + " has no accessible two-argument constructor.");
        } catch (InvocationTargetException e) {
            throw new IllegalArgumentException(strategy.getName() + " has no accessible two-argument constructor.");
        } catch (NoSuchMethodException e) {
            throw new IllegalArgumentException(strategy.getName() + " has no accessible two-argument constructor.");
        }
    }

    /**
     * Returns true if m takes no arguments.
     *
     * @return true if m takes no arguments
     **/
    public static boolean noArgs(Method m) {
        return m.getParameterTypes().length == 0;
    }

    /**
     * Returns true if m returns a formula.
     *
     * @return true if m returns a formula
     **/
    public static boolean returnsFormula(Method m) {
        return Formula.class.isAssignableFrom(m.getReturnType());
    }

    // -----CREATION FROM STRINGS-----//

    private static Matcher name = Pattern.compile("(.+?)\\(").matcher("");
    private static Matcher arg  = Pattern.compile("[\\(,]\\s*(.+?)\\s*[\\),]").matcher("");

    /**
     * Returns the class with the given name
     *
     * @throws IllegalArgumentException - no such class exists
     * @return class with the given name
     */
    public static Class< ? > findClass(String className) {
        try {
            return Class.forName(className);
        } catch (ClassNotFoundException e) {
            throw new IllegalArgumentException(e);
        }
    }

    /**
     * Returns all arguments in the given call, in the order in which they appear.
     *
     * @return all arguments in the given call, in the order in which they appear.
     */
    private static String[] args(String call) {
        final List<String> args = new ArrayList<String>();
        arg.reset(call);
        if (arg.find()) {
            args.add(arg.group(1));
            while (arg.find(arg.end() - 1)) {
                args.add(arg.group(1));
            }
        }
        return args.toArray(new String[args.size()]);
    }

    /**
     * Converts the given argument, represented as a string, to the given type.
     *
     * @throws RuntimeException - the conversion is not possible.
     * @return the given argument converted to the given type
     */
    @SuppressWarnings({
                       "unchecked", "rawtypes"
    } )
    private static Object convert(String arg, Class< ? > type) {
        try {
            if (type.isPrimitive()) {
                if (type == int.class) {
                    return new Integer(arg);
                } else if (type == long.class) {
                    return new Long(arg);
                } else if (type == boolean.class) {
                    return new Boolean(arg);
                } else if (type == double.class) {
                    return new Double(arg);
                } else if (type == float.class) {
                    return new Float(arg);
                } else if (type == byte.class) {
                    return new Byte(arg);
                } else if (type == short.class) {
                    return new Short(arg);
                } else if (type == char.class && arg.length() == 1) {
                    return new Character(arg.charAt(0));
                } else {
                    throw new IllegalArgumentException("Unknown primitive type: " + type);
                }
            } else if (type == String.class) {
                return arg;
            } else if (type.isEnum()) {
                return Enum.valueOf((Class) type, arg);
            } else if (Number.class.isAssignableFrom(type) || type == Boolean.class) {
                final Constructor< ? > c = type.getConstructor(String.class);
                return c.newInstance(arg);
            } else if (type == Character.class && arg.length() == 1) {
                return new Character(arg.charAt(0));
            }
        } catch (NoSuchMethodException e) {} catch (IllegalAccessException e) {} catch (InstantiationException e) {} catch (InvocationTargetException e) {}

        throw new IllegalArgumentException();
    }

    /**
     * Converts the given arguments, represented as strings, to appropriate types,
     * if possible. If not returns null.
     *
     * @requires args.length = argTypes.length
     * @return an array containing the given arguments, converted to appropriate
     *         types, if possible; null if not.
     */
    private static Object[] convert(String[] args, Class< ? >[] argTypes) {
        assert args.length == argTypes.length;
        final Object[] out = new Object[args.length];
        for (int i = 0; i < args.length; i++) {
            try {
                out[i] = convert(args[i], argTypes[i]);
            } catch (RuntimeException e) {
                return null;
            }
        }
        return out;
    }

    /**
     * Reflectively performs the given invocation and returns the result.
     *
     * @requires call is of the form "name(arg1, arg2, ..., argn)" where name is the
     *           full class name of the class whose constructor is to be invoked
     *           (e.g. java.lang.Integer) and the arguments are either strings,
     *           primitives, objects corresponding to primitives (Integer, Long,
     *           etc), or publicly accessible Enums.
     * @throws IllegalArgumentException - call is not formatted as specified above,
     *             or it could not be made for some reason.
     * @return an object of type T, created reflectively from the given call String
     */
    @SuppressWarnings("unchecked" )
    public static <T> T construct(String call) {
        try {
            name.reset(call);
            if (!name.find())
                throw new IllegalArgumentException("Badly formatted call: " + call);
            final Class< ? > callClass = findClass(name.group(1));

            final String[] args = args(call);

            for (Constructor< ? > c : callClass.getConstructors()) {
                final Class< ? >[] argTypes = c.getParameterTypes();
                if (argTypes.length == args.length) {
                    final Object[] convertedArgs = convert(args, argTypes);
                    if (convertedArgs != null) {
                        return (T) c.newInstance(convertedArgs);
                    }
                }
            }

            throw new IllegalAccessException("Could not call " + call);
        } catch (InstantiationException e) {
            throw new IllegalArgumentException(e);
        } catch (IllegalAccessException e) {
            throw new IllegalArgumentException(e);
        } catch (InvocationTargetException e) {
            throw new IllegalArgumentException(e);
        }
    }

    /**
     * Reflectively performs the specified invocation and returns the result.
     *
     * @requires call is of the form "name(arg1, arg2, ..., argn)" where name is the
     *           full name of the static method to be invoked (e.g.
     *           java.lang.Integer#parseInt) and the arguments are either strings,
     *           primitives, objects corresponding to primitives (Integer, Long,
     *           etc), or publicly accessible Enums.
     * @throws IllegalArgumentException - call is not formatted as specified above,
     *             or it could not be made for some reason.
     * @return an object of type T, created reflectively from executing the given
     *         call String
     */
    @SuppressWarnings("unchecked" )
    public static <T> T create(String call) {
        try {
            name.reset(call);
            if (!name.find())
                throw new IllegalArgumentException("Badly formatted call: " + call);
            final String[] parts = name.group(1).split("#");
            if (parts.length != 2)
                throw new IllegalArgumentException("Badly formatted call: " + call);
            final Class< ? > callClass = findClass(parts[0]);

            final String[] args = args(call);

            for (Method m : callClass.getDeclaredMethods()) {
                final int mod = m.getModifiers();
                if (!(parts[1].equals(m.getName()) && Modifier.isPublic(mod) && Modifier.isStatic(mod)))
                    continue;
                final Class< ? >[] argTypes = m.getParameterTypes();
                if (argTypes.length == args.length) {
                    final Object[] convertedArgs = convert(args, argTypes);
                    if (convertedArgs != null) {
                        return (T) m.invoke(null, convertedArgs);
                    }
                }
            }

            throw new IllegalAccessException("Could not call " + call);
        } catch (IllegalAccessException e) {
            throw new IllegalArgumentException(e);
        } catch (InvocationTargetException e) {
            throw new IllegalArgumentException(e);
        }
    }

    /**
     * Reflectively performs the specified invocation on the specified instance and
     * returns the result.
     *
     * @requires call is of the form "name(arg1, arg2, ..., argn)" where name is the
     *           name of the method to be invoked on the specified object and the
     *           arguments are either strings, primitives, objects corresponding to
     *           primitives (Integer, Long, etc), or publicly accessible Enums.
     * @throws IllegalArgumentException - call is not formatted as specified above,
     *             or it could not be made for some reason.
     * @return an object of type T, created reflectively from executing the given
     *         call String on the given instance
     */
    @SuppressWarnings("unchecked" )
    public static <T> T create(Object instance, String call) {
        try {
            name.reset(call);
            if (!name.find())
                throw new IllegalArgumentException("Badly formatted call: " + call);
            final String method = name.group(1);
            final Class< ? > callClass = instance.getClass();

            final String[] args = args(call);

            for (Method m : callClass.getMethods()) {

                if (!method.equals(m.getName()))
                    continue;
                final Class< ? >[] argTypes = m.getParameterTypes();
                if (argTypes.length == args.length) {
                    final Object[] convertedArgs = convert(args, argTypes);
                    if (convertedArgs != null) {
                        return (T) m.invoke(instance, convertedArgs);
                    }
                }
            }

            throw new IllegalAccessException("Could not call " + call);
        } catch (IllegalAccessException e) {
            throw new IllegalArgumentException(e);
        } catch (InvocationTargetException e) {
            throw new IllegalArgumentException(e);
        }
    }

}
