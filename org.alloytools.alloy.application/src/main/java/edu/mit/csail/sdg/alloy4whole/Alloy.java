package edu.mit.csail.sdg.alloy4whole;

import java.io.File;
import java.io.IOException;
import java.lang.reflect.Method;
import java.net.URL;
import java.util.Enumeration;

import aQute.lib.io.IO;

public class Alloy {

    static ClassLoader old = Alloy.class.getClassLoader();

    static class AlloyClassLoader extends ClassLoader {

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
            String mapped = System.mapLibraryName(libname);
            String path = System.getProperty("alloy.binary") + File.separator + mapped;
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

    }

    public static void main(String args[]) throws Exception {
        AlloyClassLoader l1 = new AlloyClassLoader();

        Class< ? > simpleGui = l1.loadClass("edu.mit.csail.sdg.alloy4whole.SimpleGUI");
        Method main = simpleGui.getMethod("main", String[].class);
        main.invoke(null, (Object) args);
    }
}
