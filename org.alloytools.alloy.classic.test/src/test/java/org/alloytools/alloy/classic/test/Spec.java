package org.alloytools.alloy.classic.test;

import java.lang.reflect.Constructor;
import java.lang.reflect.Executable;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.lang.reflect.Parameter;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.Type;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.function.Supplier;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.alloytools.alloy.core.api.Alloy;
import org.alloytools.alloy.core.api.IAtom;
import org.alloytools.alloy.core.api.IAtom.BasicType;
import org.alloytools.alloy.core.api.IRelation;
import org.alloytools.alloy.core.api.Instance;
import org.alloytools.alloy.core.api.Module;
import org.alloytools.alloy.core.api.Solution;
import org.alloytools.alloy.core.api.TField;
import org.alloytools.alloy.core.api.TFunction;

import aQute.lib.converter.Converter;

public class Spec {

    public interface MakeObject<T> {

        T make(Instance inst, IAtom root) throws Exception;
    }

    final Map<String,MakeObject< ? >> creates = new HashMap<>();
    final Alloy                       alloy;
    private boolean                   debug;


    public Spec(Alloy alloy) {
        this.alloy = alloy;
    }

    public void registerType(String alloyName, Class< ? > clazz) {
        creates.put(alloyName, (inst, atom) -> create(inst, atom, clazz));
    }

    public void registerType(String alloyName, Supplier< ? > supplier) {
        creates.put(alloyName, (inst, atom) -> supplier.get());
    }


    public void test(String source, Object test) throws Throwable {
        if (debug)
            System.out.println(source);
        for (Method m : test.getClass().getMethods()) {
            if (m.getDeclaringClass() == Object.class)
                continue;


            Solution s = alloy.getSolution(source + "\nrun " + m.getName() + "\n");

            for (Instance inst : s) {
                Map<String,Object> values = parameters(m, inst);
                try {
                    if (debug) {
                        System.out.println(m.getName() + " " + values);
                    }
                    Object[] array = values.values().toArray();
                    m.invoke(test, array);
                } catch (InvocationTargetException e) {
                    throw new AssertionError(m.getName() + " " + values + "\n" + e.getTargetException().getMessage(), e.getTargetException());
                } catch (Exception e) {
                    throw new AssertionError(m.getName() + " " + values + "\n" + e.getMessage(), e);
                }
            }
        }
    }


    class Action {

        final String    name;
        final Method    method;
        final TFunction pred;
        final int       arityWithReturn;
        final String    id;

        Action(Method method, TFunction pred, int arity) {
            this.name = method.getName();
            this.method = method;
            this.pred = pred;
            this.arityWithReturn = arity;
            this.id = "_" + this.name + "_" + arity;
        }
    }

    public <T> void testvar(String source, Class<T> type, T __, String sig) throws Throwable {
        Module module = alloy.compiler().compileSource(source);
        if (!module.isValid())
            throw new IllegalArgumentException(module.toString());

        List<Action> actions = new ArrayList<>();
        int maxpars = 0;
        for (Method m : type.getMethods()) {
            int arity = m.getParameterCount();
            if (m.getReturnType() != void.class)
                arity++;

            Optional<TFunction> function = module.getFunction(m.getName(), arity);
            if (function.isPresent() && function.get().isPredicate()) {
                Action a = new Action(m, function.get(), arity);
                actions.add(a);
                maxpars = Math.max(maxpars, a.arityWithReturn);
            }
        }

        StringBuilder sb = new StringBuilder(source);
        sb.append("\n\n***********\n");

        sb.append("private enum _actions { ");
        String del = "";
        for (Action a : actions) {
            sb.append(del).append(a.id);
            del = ", ";
        }
        sb.append("}");

        sb.append("private var sig _cmds in _actions {}\n");
        sb.append("private var one sig _cmd in _actions {}\n");
        del = "var sig ";
        for (int i = 0; i < maxpars; i++) {
            sb.append(del).append("_p").append(i);
            del = ", ";
        }
        sb.append(" in univ {}\n");
        sb.append("private one var sig _ in " + sig + " {}\n");

        sb.append("run _run {\n");

        sb.append("}\n");


    }

    private Map<String,Object> parameters(Executable m, Instance inst) throws Exception {
        IdentityHashMap<IAtom,Object> identities = new IdentityHashMap<>();
        LinkedHashMap<String,Object> map = new LinkedHashMap<>();
        for (Parameter p : m.getParameters()) {
            if (p.getName().matches("arg\\d+"))
                throw new IllegalArgumentException("You must compile the test code with the option be able to reflect on method parameters");
            IRelation variable = inst.getVariable(m.getName(), p.getName());
            Object o = convert(identities, inst, p.getParameterizedType(), variable);
            map.put(p.getName(), o);
        }
        return map;
    }


    private Object convert(IdentityHashMap<IAtom,Object> identities, Instance inst, Type type, IRelation value) throws Exception {
        Converter c = new Converter();
        c.hook(null, (t, o) -> {
            return cnv(identities, inst, type, o);
        });

        if (value.arity() == 0) {
            return c.convert(type, Collections.emptyList());
        }

        if (value.arity() == 1) {
            List<IAtom> list = value.asList();
            if (list.size() == 1 && !isCollection(type)) {
                return c.convert(type, list.get(0));
            } else {
                return c.convert(type, list);
            }
        }

        throw new IllegalArgumentException("arity of " + value.arity() + " too high, not implemented yet");
    }

    private boolean isCollection(Type type) {
        if (type instanceof Class) {
            if (Iterable.class.isAssignableFrom((Class< ? >) type)) {
                return true;
            }
            if (((Class< ? >) type).isArray()) {
                return true;
            }
        } else if (type instanceof ParameterizedType) {
            return isCollection(((ParameterizedType) type).getRawType());
        }
        return false;
    }

    private Object cnv(IdentityHashMap<IAtom,Object> identities, Instance inst, Type type, Object o) throws Exception {
        if (o instanceof IRelation) {
            return convert(identities, inst, type, (IRelation) o);
        }
        if (!(o instanceof IAtom)) {
            return null;
        }


        IAtom atom = (IAtom) o;
        if (identities.containsKey(atom))
            return identities.get(atom);

        Object converted = cnv(inst, type, atom);
        identities.put(atom, converted);
        return converted;
    }

    private Object cnv(Instance inst, Type type, IAtom atom) throws Exception, Error {
        switch (atom.getBasicType()) {
            case BOOLEAN :
            case NUMBER :
            case STRING :
                Object v = atom.natural();
                return Converter.cnv(type, v);

            case IDENTIFIER :
            case OBJECT :
                String name = atom.getSig().getName();
                MakeObject< ? > make = creates.get(name);
                if (make == null) {
                    if (atom.getBasicType() == BasicType.IDENTIFIER)
                        return atom;
                    throw new IllegalArgumentException("no class registered for sig " + name);
                }
                return make.make(inst, atom);

            default :
                throw new Error("someone aaded a new enum field in IAtom.BasicType");
        }
    }



    private Object create(Instance inst, IAtom atom, Class< ? > clazz) throws Exception {

        Map<TField,IRelation> data = inst.getObject(atom);

        List<Executable> list = Stream.concat(Stream.of(clazz.getMethods()).filter(m -> Modifier.isStatic(m.getModifiers())), Stream.of(clazz.getConstructors())).filter(e -> e.getParameterCount() == data.size()).collect(Collectors.toList());

        for (Executable e : list) {
            Object[] vs = parameters(e, inst).values().toArray();
            if (e instanceof Method) {
                return ((Method) e).invoke(null, vs);
            } else
                return ((Constructor< ? >) e).newInstance(vs);
        }
        return clazz.newInstance();
    }

    public void debug() {
        this.debug = true;
    }

}
