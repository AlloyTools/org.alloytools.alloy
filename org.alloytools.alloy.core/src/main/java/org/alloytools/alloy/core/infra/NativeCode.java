package org.alloytools.alloy.core.infra;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.nio.file.Files;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;
import java.util.regex.Pattern;

import aQute.lib.io.IO;

/**
 * @author AlloyTools
 * @author Nuno Macedo // [pardinus] find executable binaries
 */
public class NativeCode {

    final static Set<File> PATH = new HashSet<>();
    final static File      cache;

    static {
        try {
            cache = Files.createTempDirectory("alloy-").toFile();
        } catch (IOException e) {
            RuntimeException runtimeException = new RuntimeException("Failed to create temporary directory for binaries");
            System.err.println(runtimeException);
            throw runtimeException;
        }
    }

    static class Platform {

        final String                  id;
        final Function<String,String> mapLibrary;
        final Function<String,String> mapExe;
        final Pattern                 osname;
        final Pattern                 osarch;
        final String                  dir;


        public Platform(String id, String osnames, String osarch, String dir, Function<String,String> mapLibrary, Function<String,String> mapExe) {
            this.id = id;
            this.mapLibrary = mapLibrary;
            this.mapExe = mapExe;
            try {
                this.osarch = Pattern.compile(osarch, Pattern.CASE_INSENSITIVE);
                this.osname = Pattern.compile(osnames, Pattern.CASE_INSENSITIVE);
                this.dir = dir;
            } catch (Exception e) {
                e.printStackTrace();
                throw new RuntimeException(e);
            }
        }

        public String mapLibrary(String base) {
            return mapLibrary.apply(base);
        }

        public String mapExe(String base) {
            return mapExe.apply(base);
        }

        @Override
        public String toString() {
            return id;
        }
    }

    static Map<String,File>  cached      = new HashMap<>();

    public static Platform   AMD64_LINUX = new Platform("Linux/amd64", "linux", "amd64", "amd64-linux", s -> "lib" + s + ".so", s -> s);
    public static Platform   ARM_MAC     = new Platform("MacOS Apple", "mac\\s*os.*", "aarch64", "arm-mac", s -> "lib" + s + ".dylib", s -> s);
    public static Platform   X86_MAC     = new Platform("MacOS Intel", "mac\\s*os.*", "ppc|power|powerpc.*|x86.*", "x86-mac", s -> "lib" + s + ".dylib", s -> s);
    public static Platform   X86_WINDOWS = new Platform("Windows/x86", "win.*", "x86.*|amd64", "x86-windows", s -> s + ".dll", s -> s + ".exe");
    public static Platform   X86_LINUX   = new Platform("Linux/x86", "linux", ".*86.*", "x86-linux", s -> "lib" + s + ".so", s -> s);

    public static Platform[] platforms   = {
                                            AMD64_LINUX, X86_LINUX, X86_MAC, X86_WINDOWS, ARM_MAC
    };

    public static Platform   platform    = findPlatform();

    public static synchronized File findexecutable(String name) throws RuntimeException {
        return findexecutable(platform, name);
    }

    public static synchronized File findexecutable(Platform platform, String name) throws RuntimeException {
        try {

            Platform p = platform;

            String file = platform.dir + "/" + name;
            Enumeration<URL> enumeration = NativeCode.class.getClassLoader().getResources(file);
            if (!enumeration.hasMoreElements()) {
                return null;
            }
            URL resource = enumeration.nextElement();

            File to = cached.computeIfAbsent(name, (k) -> {

                try {
                    File tox = new File(cache, name);
                    tox.deleteOnExit();
                    IO.copy(resource, tox);
                    return tox;
                } catch (IOException e) {
                    throw new RuntimeException(e);
                }
            });

            to.setExecutable(true);
            return to;

        } catch (IOException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    private static Platform findPlatform() {
        String os = System.getProperty("os.name");
        String arch = System.getProperty("os.arch");
        //        System.out.println("OS _ ARCH = '" + os + "' - '" + arch + "'");
        for (Platform p : platforms) {
            if (p.osarch.matcher(arch).matches() && p.osname.matcher(os).matches()) {
                //                System.out.println("Found = '" + p.dir);
                return platform = p;
            }
        }
        return new Platform("UNKNOWN-" + os + "/" + arch, ".*", ".*", null, s -> s, s -> s);
    }



    static {
        String libraryPath = System.getProperty("java.library.path");
        if (libraryPath != null) {
            for (String s : libraryPath.split(File.pathSeparator)) {
                File dir = new File(s);
                if (dir.isDirectory())
                    PATH.add(dir);
            }
        }
        String path = System.getenv("PATH");
        if (path != null) {
            for (String s : path.split(File.pathSeparator)) {
                File dir = new File(s);
                if (dir.isDirectory())
                    PATH.add(dir);
            }
        }
    }


    public static boolean library(String string) {
        try {
            System.loadLibrary(string);
            return true;
        } catch (java.lang.UnsatisfiedLinkError e) {
            return false;
        }
    }

    public static Optional<File> executable(String name) {
        if (IO.isWindows()) {
            name = name + ".exe";
        }
        for (File dir : PATH) {
            File file = new File(dir, name);
            if (file.canExecute())
                return Optional.of(file);
        }
        return Optional.ofNullable(findexecutable(name));
    }
}
