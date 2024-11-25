package kodkod.solvers.api;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.nio.file.FileVisitResult;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.SimpleFileVisitor;
import java.nio.file.StandardCopyOption;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.function.Function;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import aQute.lib.collections.ExtList;
import aQute.lib.io.IO;
import aQute.lib.strings.Strings;

/**
 * Alloy Native code
 * 
 * In Alloy, we use native code and carry the code in the application. This code
 * is extracted before it is used. Both executables and libraries are supported.
 * 
 * Both libraries and executables have a generic name for a lib/exe. This
 * generic name is then mapped to a name used on the platform. For example, a
 * unix library will be libGENERICNAME.so.
 * 
 * For both exe and and lib, we first look up if the environment provides an
 * instance.
 * 
 * <ul>
 * <li>First look up a property with the name "alloy.library." + generic name.
 * <ul>
 * <li>NO – report this exe/lib as unavailable
 * <li>path to file – If this file exists, use it. Otherwise continue.
 * <li>null – continue
 * </ul>
 * <li>Map the generic name to the local platform name. Find this platform name
 * on the `java.library.path` property for libraries and the environment PATH
 * for executables. If found there, use it. I.e. the environment has priority.
 * Otherwise continue
 * <li>Locate the platform name in the JARs based on the current platform. Each
 * supported platform has a prefix that we use to locat it. If we find the
 * entry, we copy it to a cache directory and use it.
 * </ul>
 */
public class NativeCode {
	final static Logger logger = LoggerFactory.getLogger(NativeCode.class);
	final static Set<File> PATH = new LinkedHashSet<>();
	final static Set<File> LIBRARYPATH = new LinkedHashSet<>();
	final static File cache;

	static {
		logger.debug("adding native-code cleanup hook");
		Runtime.getRuntime().addShutdownHook(new Thread(NativeCode::close, "native-code-cleanup") {
		});
		String libraryPath = System.getProperty("java.library.path");
		if (libraryPath != null) {
			logger.debug("processing 'java.library.path' {}", libraryPath);
			for (String s : libraryPath.split(File.pathSeparator)) {
				File dir = new File(s);
				if (dir.isDirectory()) {
					LIBRARYPATH.add(dir);
				} else {
					logger.info("entry {} not a directory, not added to LIBRARYPATH", dir.getAbsolutePath());
				}
			}
		} else 
			logger.info("no 'java.library.path' set");
			
		String path = System.getenv("PATH");
		if (path != null) {
			logger.debug("processing env 'PATH' {}", path);
			for (String s : path.split(File.pathSeparator)) {
				File dir = new File(s);
				if (dir.isDirectory()) {
					PATH.add(dir);
				} else {
					logger.info("entry {} not a directory, not added to PATH", dir.getAbsolutePath());
				}
			}
		}

		try {
			cache = Files.createTempDirectory("alloy-").toFile();
			LIBRARYPATH.add(cache);
			PATH.add(cache);
		} catch (IOException e) {
			logger.error("Could not create temp directory {}", e, e);
			RuntimeException runtimeException = new RuntimeException(
					"Failed to create temporary directory for binaries");
			System.err.println(runtimeException);
			throw runtimeException;
		}
		logger.debug("LIBRARYPATH {} PATH {} cache={}", LIBRARYPATH, PATH, cache);
	}

	public static class Platform {

		final String id;
		final Function<String, String> mapLibrary;
		final Function<String, String> mapExe;
		final Pattern osname;
		final Pattern osarch;

		public Platform(String id, String osnames, String osarch, Function<String, String> mapLibrary,
				Function<String, String> mapExe) {
			this.id = id;
			this.mapLibrary = mapLibrary;
			this.mapExe = mapExe;
			try {
				this.osarch = Pattern.compile(osarch, Pattern.CASE_INSENSITIVE);
				this.osname = Pattern.compile(osnames, Pattern.CASE_INSENSITIVE);
			} catch (Exception e) {
				logger.error("failed to compile pattern for osnames or osarch, either {} or {} ", osnames, osarch);
				throw new RuntimeException(e);
			}
		}

		public String mapLibrary(String base) {
			String mappedName = mapLibrary.apply(base);
			logger.debug("mapLibrary from {} to {}",base, mappedName);			
			return mappedName;
		}

		public String mapExe(String base) {
			String mappedName = mapExe.apply(base);
			logger.debug("mapExe from {} to {}",base, mappedName);			
			return mappedName;
		}

		@Override
		public String toString() {
			return id;
		}

		public Optional<File> getExecutable(String genericName) {
			String key = "alloy.native.exe." + genericName;
			String path = System.getProperty(key);
			if (path != null) {
				if (path.equals("NO")) {
					logger.warn("getExecutable requested to ignore native exe {}", genericName);
					return Optional.empty();
				}
				File f = IO.getFile(path);
				if (f.isFile()) {
					logger.debug("getExecutable uses system property {}={}",key, f.getAbsolutePath());			
					return Optional.of(f);
				}
				logger.warn(
						"getExecutable for the generic exe {}, a property alloy.native.exe.{} was found: {} but this was not a proper file. Trying to find it on the path or internal",
						genericName, path, f.getAbsolutePath());
			}
			String exe = mapExe.apply(genericName);
			logger.debug("getExecutable stem exe = {}",exe);			

			for (File dir : PATH) {
				File file = new File(dir, genericName);
				if (file.canExecute()) {
					logger.debug("getExecutable found in path  {}",file.getAbsolutePath());			
					return Optional.of(file);
				}
			}

			File file = new File(cache, exe);
			if (!file.canExecute()) {				
				if (!extract(exe, file)) {
					logger.debug("getExecutable file not found and not found in the JAR {}",exe);			
					return Optional.empty();
				}
				file.setExecutable(true);
				logger.debug("getExecutable extracted {}",exe);			
			}
			logger.debug("getExecutable file for {} found {}",exe, file.getAbsolutePath());			
			return Optional.of(file);
		}

		public Optional<File> getLibrary(String genericName) {
			String path = System.getProperty("alloy.native.lib." + genericName);

			if (path != null) {
				logger.debug("getLibrary `alloy.native.lib` system property {}",path);			
				if (path.equals("NO")) {
					logger.warn("getLibrary requested to ignore native lib {} with NO in `alloy.native.lib`", genericName);
					return Optional.empty();
				}
				File f = new File(path);
				if (f.isFile()) {
					logger.debug("getLibrary found file for {}",path);			
					return Optional.of(f);
				}

				logger.warn(
						"getLibrary for the generic lib {}, a property alloy.native.lib.{} was found: {} but this was not a proper file. Trying to find it on the path or internal",
						genericName, path, f.getAbsolutePath());
			}

			String lib = mapLibrary.apply(genericName);
			logger.debug("getLibrary mapping generic name to library name {}={}",genericName, lib);			

			File file = new File(cache, lib);
			if (file.isFile()) {
				logger.debug("getLibrary found {}={} (cache)",genericName, file.getAbsolutePath());			
				return Optional.of(file);
			}

			if (extract(lib, file)) {
				logger.debug("getLibrary extracted {}={}",genericName, file.getAbsolutePath());			
				file.setExecutable(true);
				return Optional.of(file);
			}

			for (File dir : LIBRARYPATH) {
				file = new File(dir, lib);
				if (file.isFile()) {
					logger.debug("getLibrary found in library path {}={}",genericName, file.getAbsolutePath());			
					return Optional.of(file);
				} 
			}
			logger.info("getLibrary  not found {}/{} in cache({}) embedded({}) libpath({})",genericName, lib, cache.list(), embedded(), LIBRARYPATH );			
			return Optional.empty();
		}

		public String embedded() {
			try {
				URL receipt = Platform.class.getClassLoader().getResource("native/receipt");
				if ( receipt == null) {
					return "no 'native/receipt' resource";
				}
				String data = IO.collect(receipt.openStream());
				if ( data == null) {
					return "no 'native/receipt' data";
				}
				
				String prefix = "native/"+id;
				return Strings.splitAsStream(data).filter(s -> s.startsWith(prefix)).collect(Collectors.joining());
			} catch( Exception e) {
				logger.error("failed to parse receipt {}", e, e);
				return "no valid native/rececipt in jar";
			}
		}

		public boolean extract(String actualName, File file) {
			String resource = "native/" + id + "/" + actualName;

			try {

				URL url = Platform.class.getClassLoader().getResource(resource);
				if (url == null) {
					logger.info("extract library {} not found to extract",resource);			
					return false;
				}

				Path to = file.toPath();
				Files.copy(url.openStream(), to, StandardCopyOption.REPLACE_EXISTING);
				file.deleteOnExit();
				logger.debug("extract library {} extracted to {}",url, to);			
				return true;
			} catch (Exception e) {
				logger.error("extract failed to extract native code from the jar. name=%s, file=%s: %s", actualName, file, e,
						e);
				return false;
			}
		}

		public boolean isPresentExe(String name) {
			return getExecutable(name).isPresent();
		}

		public boolean isPresentlib(String name) {
			return getExecutable(name).isPresent();
		}
	}

	static Map<String, File> cached = new HashMap<>();

	public static Platform LINUX_X86_64 = new Platform("linux/amd64", "linux", "amd64", s -> "lib" + s + ".so", s -> s);
	public static Platform DARWIN_ARM64 = new Platform("darwin/arm64", "mac\\s*os.*", "aarch64",
			s -> "lib" + s + ".dylib", s -> s);
	public static Platform DARWIN_AMD64 = new Platform("darwin/amd64", "mac\\s*os.*", "ppc|power|powerpc.*|x86.*",
			s -> "lib" + s + ".dylib", s -> s);

	public static Platform WINDOWS_AMD64 = new Platform("windows/amd64", "win.*", "x86.*|amd64", s -> s + ".dll",
			s -> s + ".exe");

	public static Platform[] platforms = { LINUX_X86_64, DARWIN_ARM64, DARWIN_AMD64, WINDOWS_AMD64 };

	public static Platform platform = findPlatform();

	public static Optional<File> getLibrary(String libname) {
		return platform.getLibrary(libname);
	}
	private static Platform findPlatform() {
		String os = System.getProperty("os.name");
		String arch = System.getProperty("os.arch");
		for (Platform p : platforms) {
			if (p.osarch.matcher(arch).matches() && p.osname.matcher(os).matches()) {
				logger.debug("findPlatform {}", p);
				return platform = p;
			}
		}
		logger.error("findPlatform unknown {} {}", os, arch);
		return new Platform("UNKNOWN-" + os + "/" + arch, ".*", ".*", s -> s, s -> s);
	}

	public static void clearCache() {
		logger.debug("clearCache {}", new ExtList<>(cache.listFiles()));
		for (File f : cache.listFiles()) {
			f.delete();
		}
	}

	public static String getLibraryPath() {
		return LIBRARYPATH.stream().map(File::getAbsolutePath).collect(Collectors.joining(File.pathSeparator));
	}

	final static AtomicBoolean closing = new AtomicBoolean(false);

	public static void close() {
		if (closing.getAndSet(true))
			return;
		logger.debug("close");
		try {
			Files.walkFileTree(cache.toPath(), new SimpleFileVisitor<Path>() {
				@Override
				public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) throws IOException {
					Files.deleteIfExists(file);
					return super.visitFile(file, attrs);
				}

				@Override
				public FileVisitResult postVisitDirectory(Path dir, IOException exc) throws IOException {
					Files.delete(dir);
					return super.postVisitDirectory(dir, exc);
				}
			});
		} catch (IOException e) {
			// ignore
		}
	}

}
