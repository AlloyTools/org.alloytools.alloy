package org.alloytools.alloy.core;

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
		debug = "yes".equalsIgnoreCase(System.getProperty("debug"))
				|| "true".equalsIgnoreCase(System.getProperty("debug"));
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
}
