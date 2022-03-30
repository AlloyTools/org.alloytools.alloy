package org.alloytools.metainf.util;

import java.io.IOException;
import java.net.URL;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.jar.Manifest;

import aQute.bnd.exceptions.Exceptions;
import aQute.libg.parameters.ParameterMap;

public class ManifestAccess {

    final static Map<String,Manifest> manifests = new HashMap<>();
    final static Map<String,String>   headers   = new ConcurrentHashMap<>();
    static {
        try {
            Enumeration<URL> resources = ManifestAccess.class.getClassLoader().getResources("META-INF/MANIFEST.MF");
            if (resources != null) {
                while (resources.hasMoreElements()) {
                    URL url = resources.nextElement();
                    Manifest m = new Manifest(url.openStream());
                    String bsn = m.getMainAttributes().getValue("Bundle-SymbolicName");
                    if (bsn != null) {
                        manifests.put(bsn, m);
                    }
                }
            }
        } catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    public static Optional<String> getHeader(String bsn, String header) {
        Manifest m = manifests.get(bsn);
        if (m == null)
            return Optional.empty();

        String value = m.getMainAttributes().getValue(header);
        return Optional.ofNullable(value);
    }

    public static Set<String> getBsns() {
        return manifests.keySet();
    }

    public static String getVersion(String bsn) {
        return getHeader(bsn, "Bundle-Version").orElse(null);
    }


    public static ParameterMap getParameterHeader(String key) throws IOException {
        String result = headers.computeIfAbsent(key, k -> {
            StringBuilder sb = new StringBuilder();
            try {
                Enumeration<URL> resources = ManifestAccess.class.getClassLoader().getResources("META-INF/MANIFEST.MF");
                while (resources.hasMoreElements())
                    try {
                        URL url = resources.nextElement();
                        System.out.println("header " + url + " ");
                        Manifest m = new Manifest(url.openStream());
                        String value = m.getMainAttributes().getValue(key);
                        if (value != null) {
                            if (sb.length() != 0)
                                sb.append(",");
                            sb.append(value);
                        }
                    } catch (Exception e) {
                        // ignore
                    }
            } catch (IOException e1) {
                throw Exceptions.duck(e1);
            }
            return sb.toString();
        });
        return new ParameterMap(result);
    }

}
