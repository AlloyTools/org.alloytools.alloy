package org.alloytools.metainf.util;

import java.io.IOException;
import java.net.URL;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.jar.Manifest;

public class ManifestAccess {

	final static Map<String, Manifest> manifests = new HashMap<>();
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

}
