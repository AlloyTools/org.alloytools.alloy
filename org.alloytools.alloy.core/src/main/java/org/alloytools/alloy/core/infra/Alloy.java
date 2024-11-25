package org.alloytools.alloy.core.infra;

import java.io.File;
import java.io.IOException;
import java.lang.reflect.Method;
import java.net.URL;
import java.util.Enumeration;
import java.util.Optional;
import java.util.function.Function;

import aQute.lib.io.IO;

/**
 * This class is the main class for the JAR. Its name is the name shown in the
 * GUI on MacOS, so do not change it.
 * <p>
 * This class is an entry point and should not be renamed. It should also _NOT_
 * touch any other classes. We're creating a special class loader to allow the
 * dynamic libraries to be found. If you link this class to any other class
 * you're bound to create trouble.
 *
 */
public class Alloy {

    static ClassLoader                     old = Alloy.class.getClassLoader();
    static Function<String,Optional<File>> getLibrary;

    static class AlloyClassLoader extends ClassLoader implements AutoCloseable {

        AlloyClassLoader() {
            super(null);
        }

        @Override
        public URL findResource(String name) {
            return old.getResource(name);
        }

        @Override
        public Enumeration<URL> findResources(String name) throws IOException {
            return old.getResources(name);
        }

        @Override
        protected String findLibrary(String libname) {
            Optional<File> f = getLibrary.apply(libname);
            String path = f.map(File::getAbsolutePath).orElse(null);
            return path;
        }

        @Override
        protected Class< ? > findClass(String name) throws ClassNotFoundException {
            URL url = findResource(name.replace('.', '/') + ".class");
            if (url == null)
                throw new ClassNotFoundException(name);

            try {
                byte[] read = IO.read(url);
                return defineClass(name, read, 0, read.length);
            } catch (Exception e) {
                throw new ClassNotFoundException(name, e);
            }
        }

        @Override
        public void close() throws Exception {
        }

    }

    @SuppressWarnings("unchecked" )
    public static void main(String args[]) throws Exception {
        try (AlloyClassLoader l1 = new AlloyClassLoader()) {
            Class< ? > nativeCode = l1.loadClass("kodkod.solvers.api.NativeCode");
            Method method = nativeCode.getMethod("getLibrary", String.class);
            getLibrary = name -> {
                try {
                    return (Optional<File>) method.invoke(null, name);
                } catch (Throwable t) {
                    throw new RuntimeException(t);
                }
            };
            Class< ? > dispatcher = l1.loadClass("org.alloytools.alloy.core.infra.AlloyDispatcher");
            Method main = dispatcher.getMethod("main", String[].class);
            main.invoke(null, (Object) args);
        }
    }
}
