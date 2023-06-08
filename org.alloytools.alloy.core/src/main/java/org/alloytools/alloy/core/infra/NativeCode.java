package org.alloytools.alloy.core.infra;

import java.io.IOException;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.util.Enumeration;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.regex.Pattern;

/**
 * @author AlloyTools
 * @author Nuno Macedo // [pardinus] find executable binaries
 */
public class NativeCode {

    static class Platform {

        public Platform(String osnames, String osarch, String dir) {
            try {
                this.osarch = Pattern.compile(osarch, Pattern.CASE_INSENSITIVE);
                this.osname = Pattern.compile(osnames, Pattern.CASE_INSENSITIVE);
                this.dir = dir;
            } catch (Exception e) {
                e.printStackTrace();
                throw new RuntimeException(e);
            }
        }

        final Pattern osname;
        final Pattern osarch;
        final String  dir;

        @Override
        public String toString() {
            return osname + "/" + osarch + " " + dir;
        }
    }

    static Map<String,Path>  cached      = new ConcurrentHashMap<>();

    public static Platform   AMD64_LINUX = new Platform("linux", "amd64", "amd64-linux");
    public static Platform   X86_LINUX   = new Platform("linux", ".*86.*", "x86-linux");
    public static Platform   X86_MAC     = new Platform("mac\\s*os.*", "ppc|power|powerpc.*|x86.*", "x86-mac");
    public static Platform   X86_WINDOWS = new Platform("win.*", "x86.*|amd64", "x86-windows");
    public static Platform   ARM_MAC     = new Platform("mac\\s*os.*", "aarch64", "arm-mac");
    public static Platform[] platforms   = {
                                            AMD64_LINUX, X86_LINUX, X86_MAC, X86_WINDOWS, ARM_MAC
    };

    public static Platform   platform    = findPlatform();

    public static String findexecutable(Path cache, String name) throws RuntimeException {
        try {
            if (platform.dir == null) {
                System.out.println("cannot determine platform");
                return null;
            }

            Platform p = platform;
            String libraryName = name;

            String file = platform.dir + "/" + libraryName;
            Enumeration<URL> enumeration = NativeCode.class.getClassLoader().getResources(file);
            if (!enumeration.hasMoreElements()) {
                System.out.println("No binary resource for " + file);
                return null;
            }
            URL resource = enumeration.nextElement();

            Path to = cached.computeIfAbsent(name, (k) -> {
                try {
                    if (cache == null) {
                        Path tox = Files.createTempFile(name, libraryName);
                        tox.toFile().deleteOnExit();
                        Files.copy(resource.openStream(), tox, StandardCopyOption.REPLACE_EXISTING);
                        return tox;
                    } else {
                        cache.toFile().mkdirs();
                        return cache.resolve(libraryName);
                    }
                } catch (IOException e) {
                    throw new RuntimeException(e);
                }
            });

            to.toFile().setExecutable(true);
            if (!to.toFile().canExecute()) {
                System.out.println("binary " + to + " for " + platform.dir + " cannot be set to executable");

            }
            return to.toFile().getAbsolutePath();

        } catch (IOException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    @SuppressWarnings("unused" )
    public static boolean loadlibrary(Path cache, String name) throws RuntimeException {
        try {
            if (platform.dir == null)
                return false;

            Platform p = platform;
            String libraryName = System.mapLibraryName(name);

            String file = platform.dir + "/" + libraryName;
            Enumeration<URL> enumeration = NativeCode.class.getClassLoader().getResources(file);
            if (!enumeration.hasMoreElements()) {
                return false;
            }

            URL resource = enumeration.nextElement();

            Path to = cached.computeIfAbsent(name, (k) -> {
                try {
                    if (cache == null) {
                        Path tox = Files.createTempFile(name, libraryName);
                        tox.toFile().deleteOnExit();
                        return tox;
                    } else {
                        cache.toFile().mkdirs();
                        return cache.resolve(libraryName);
                    }
                } catch (IOException e) {
                    throw new RuntimeException(e);
                }
            });

            Files.copy(resource.openStream(), to, StandardCopyOption.REPLACE_EXISTING);
            System.load(to.toFile().getAbsolutePath());
            return true;
        } catch (IOException e) {
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
        System.out.println("canot determine platform for " + os + " " + arch);
        return new Platform(".*", ".*", null);
    }
}
