package org.alloytools.alloy.core;

import java.io.File;

/**
 * Class for globally accessible things.
 *
 */
public class AlloyCore {

    interface RunnableWithException {

        void run() throws Exception;
    }

    final static boolean debug;
    static {
        String debugString = System.getProperty("debug");
        debug = "yes".equalsIgnoreCase(debugString) || "true".equalsIgnoreCase(debugString);
    }

    public static boolean isDebug() {
        return debug;
    }

    public static void isDebug(RunnableWithException r) {
        try {
            if (isDebug())
                r.run();
        } catch (Exception e) {
            // ignore, only running in debug mode
        }
    }


    public static boolean isWindows() {
        return File.separatorChar == '\\';
    }
}
