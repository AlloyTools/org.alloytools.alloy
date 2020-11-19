/* Alloy Analyzer 4 -- Copyright (c) 2006-2009, Felix Chang
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files
 * (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify,
 * merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
 * OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package edu.mit.csail.sdg.alloy4;

import java.io.IOException;
import java.net.URL;
import java.time.Instant;
import java.util.Enumeration;
import java.util.jar.Manifest;

/**
 * This holds the buildDate String. The release build script will generate a
 * customized Version.java with the correct buildnumber and date.
 * <p>
 * <b>Thread Safety:</b> Safe.
 */

public final class Version {

    /**
     * The constructor is private, since this class never needs to be instantiated.
     */
    private Version() {
    }

    public static String  version      = "unknown";
    public static long    buildnumber  = -1;
    public static Instant builddate    = Instant.ofEpochMilli(0);
    public static String  commit       = "unknown";
    public static boolean experimental = true;
    private static String shortversion = "";

    static {
        Manifest manifest = getManifest();
        if (manifest != null) {

            String version = manifest.getMainAttributes().getValue("Bundle-Version");
            if (version != null) {
                Version.version = version;
                int lastIndexOf = version.lastIndexOf('.');
                if (lastIndexOf > 0) {
                    Version.shortversion = version.substring(0, lastIndexOf);
                } else {
                    Version.shortversion = version;
                }
            }

            String commit = manifest.getMainAttributes().getValue("Git-SHA");
            if (commit != null)
                Version.commit = commit;

            String buildnumber = manifest.getMainAttributes().getValue("Bnd-LastModified");
            if (buildnumber != null && buildnumber.matches("\\d+")) {
                Version.buildnumber = Long.parseLong(buildnumber);
                builddate = Instant.ofEpochMilli(Version.buildnumber);
            }
        }

    }

    /**
     * This is true if this is an experimental version rather than a release
     * version.
     */

    /** Returns the build number. */
    public static long buildNumber() {
        return buildnumber;
    }

    /** Returns the version string. */
    public static String version() {
        return version;
    }

    private static Manifest getManifest() {
        try {
            Enumeration<URL> resources = Version.class.getClassLoader().getResources("META-INF/MANIFEST.MF");
            while (resources.hasMoreElements()) {
                URL url = resources.nextElement();
                Manifest m = new Manifest(url.openStream());
                String value = m.getMainAttributes().getValue("Bundle-SymbolicName");
                if (value != null && value.equals("org.alloytools.alloy.dist")) {
                    return m;
                }
            }
        } catch (IOException e) {
            // we ignore
        }

        return null;
    }

    /** Returns the build date. */
    public static String buildDate() {
        return builddate.toString();
    }

    public static String getShortversion() {
        return shortversion;
    }

}
