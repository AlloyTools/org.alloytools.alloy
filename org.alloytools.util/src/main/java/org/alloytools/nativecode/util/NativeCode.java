package org.alloytools.nativecode.util;

import java.io.IOException;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.util.Enumeration;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.regex.Pattern;

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

		final Pattern	osname;
		final Pattern	osarch;
		final String	dir;

		@Override
		public String toString() {
			return "Platform [osname=" + osname + ", osarch=" + osarch + ", dir=" + dir + "]";
		}

	}

	static Map<String, Path>	cached		= new ConcurrentHashMap<>();

	public static Platform		AMD64_LINUX	= new Platform("linux", "amd64", "amd64-linux");
	// public static Platform x86_64_LINUX = new Platform("linux", "x86-64",
	// "linux_x86_64");
	// public static Platform X86_FREEBSD = new Platform("freebsd", "x86.*",
	// "x86-freebsd");
	public static Platform		X86_LINUX	= new Platform("linux", ".*86.*", "x86-linux");
	public static Platform		X86_MAC		= new Platform("mac\\s*os.*", "ppc|power|powerpc.*|x86.*", "x86-mac");
	public static Platform		X86_WINDOWS	= new Platform("win.*", "x86.*", "x86-windows");
	public static Platform[]	platforms	= {
			AMD64_LINUX,
			// x86_64_LINUX, X86_FREEBSD,
			X86_LINUX, X86_MAC, X86_WINDOWS
	};

	public static Platform		platform	= findPlatform();

	public static boolean loadlibrary(Path cache, String name, Class<?> libraryClass) throws RuntimeException {
		if (platform.dir == null)
			return false;

		String libraryName = System.mapLibraryName(name);

		Path to = cacheBinary(cache, libraryName);
		if (to == null)
			return false;

		System.load(to.toFile().getAbsolutePath());
		return true;
	}

	public static Path cacheBinary(Path cache, String libraryName) {
		try {
			String file = platform.dir + "/" + libraryName;
			Enumeration<URL> enumeration = NativeCode.class.getClassLoader().getResources(file);
			if (!enumeration.hasMoreElements()) {
				System.out.println("Could not find native lib " + file);
				return null;
			}

			URL resource = enumeration.nextElement();

			Path to = cached.computeIfAbsent(libraryName, (k) -> {
				try {
					if (cache == null) {
						Path tox = Files.createTempFile("cache", libraryName);
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
			return to;
		} catch (IOException e) {
			throw new RuntimeException(e);
		}
	}

	static Platform findPlatform() {
		String os = System.getProperty("os.name");
		String arch = System.getProperty("os.arch");
		for (Platform p : platforms) {
			if (p.osarch.matcher(arch).matches() && p.osname.matcher(os).matches()) {
				return platform = p;
			}
		}
		return new Platform(".*", ".*", null);
	}
}
