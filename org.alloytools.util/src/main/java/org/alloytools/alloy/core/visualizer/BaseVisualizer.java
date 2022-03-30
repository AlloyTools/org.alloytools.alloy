package org.alloytools.alloy.core.visualizer;

import java.lang.reflect.ParameterizedType;
import java.lang.reflect.Type;
import java.util.ArrayList;
import java.util.List;
import java.util.function.Supplier;

import org.alloytools.alloy.core.api.Alloy;
import org.alloytools.alloy.core.api.Visualizer;

@SuppressWarnings({
                   "rawtypes", "unchecked"
} )
public abstract class BaseVisualizer implements Visualizer {

    static class Form implements RenderType {

        Supplier<Object> create;
        Class< ? >       argumentType;
        Class< ? >       outputType;

        public Form(Supplier<Object> constructor, Class< ? > argType, Class< ? > outType) {
            create = constructor;
            argumentType = argType;
            outputType = outType;
        }

        @Override

        public Class< ? > getArgumentType() {
            return argumentType;
        }

        @Override
        public Class< ? > getOutputType() {
            return outputType;
        }

        @Override
        public <A, O> Renderer<A,O> instantiate(Class<A> a, Class<O> o) {
            return (Renderer<A,O>) create.get();
        }
    }

    final Alloy      alloy;
    final List<Form> catalog = new ArrayList<Form>();

    protected BaseVisualizer(Alloy alloy, Class< ? >... renderers) {
        this.alloy = alloy;
        for (Class< ? > r : renderers) {
            Form f = getInterfaceTypeFor(r, Renderer.class);
            if (f != null) {
                catalog.add(f);
            } else {
                throw new Error("A renderer does not implement Render");
            }
        }
    }

    <T> Form getInterfaceTypeFor(Class<T> r, Class< ? > class1) {
        for (int i = 0; i < r.getInterfaces().length; i++) {
            Class< ? > rintrf = r.getInterfaces()[i];
            if (rintrf == class1) {
                ParameterizedType ptype = (ParameterizedType) r.getGenericInterfaces()[i];
                Type[] types = ptype.getActualTypeArguments();
                Class< ? > argType = (Class< ? >) types[0];
                Class< ? > outType = (Class< ? >) types[1];
                return new Form(() -> alloy.create(r), argType, outType);
            }
        }
        Class< ? super T> superclass = r.getSuperclass();
        if (superclass != Object.class)
            return getInterfaceTypeFor(superclass, class1);
        else
            return null;

    }


    @Override
    public List<RenderType> getRenderTypes() {
        return new ArrayList<>(catalog);
    }

    @Override
    public String toString() {
        return getName() + "[" + getRenderTypes() + "]";
    }


}
