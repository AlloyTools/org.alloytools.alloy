package org.alloytools.alloy.core.infra;

import java.io.File;
import java.io.IOException;
import java.lang.reflect.Method;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Enumeration;

import org.alloytools.nativecode.util.NativeCode;

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

    static ClassLoader old = Alloy.class.getClassLoader();
    static Path        cache;

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
            String mappedName = System.mapLibraryName(libname);
            String findexecutable = NativeCode.findexecutable(cache, mappedName);
            if (findexecutable != null) {
                File f = new File(findexecutable);
                if (!f.isFile()) {
                    System.out.printf("loaded library %s %s platform=%s arch=%s is not a file\n", libname, System.getProperty("os.name"), System.getProperty("os.arch"));
                    return null;
                }
                if (!f.canExecute()) {
                    System.out.printf("loaded library %s %s platform=%s arch=%s is not executable\n", libname, System.getProperty("os.name"), System.getProperty("os.arch"));
                    return null;
                }
                return findexecutable;
            }

            System.out.printf("load library failed %s platform=%s arch=%s\n", libname, System.getProperty("os.name"), System.getProperty("os.arch"));
            return null;
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
        cache = Files.createTempDirectory("alloy-");
        AlloyClassLoader l1 = new AlloyClassLoader();

        Class< ? > dispatcher = l1.loadClass("org.alloytools.alloy.core.infra.AlloyDispatcher");
        Method main = dispatcher.getMethod("main", String[].class);
        main.invoke(null, (Object) args);
    }
}
