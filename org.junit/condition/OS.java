/*
 * Copyright 2015-2021 the original author or authors.
 *
 * All rights reserved. This program and the accompanying materials are
 * made available under the terms of the Eclipse Public License v2.0 which
 * accompanies this distribution and is available at
 *
 * https://www.eclipse.org/legal/epl-v20.html
 */

package org.junit.jupiter.api.condition;

import static org.apiguardian.api.API.Status.STABLE;

import java.util.Locale;

import org.apiguardian.api.API;
import org.junit.platform.commons.logging.Logger;
import org.junit.platform.commons.logging.LoggerFactory;
import org.junit.platform.commons.util.StringUtils;

/**
 * Enumeration of common operating systems used for testing Java applications.
 *
 * <p>If the current operating system cannot be detected &mdash; for example,
 * if the {@code os.name} JVM system property is undefined &mdash; then none
 * of the constants defined in this enum will be considered to be the
 * {@linkplain #isCurrentOs current operating system}.
 *
 * @since 5.1
 * @see #AIX
 * @see #LINUX
 * @see #MAC
 * @see #SOLARIS
 * @see #WINDOWS
 * @see #OTHER
 * @see EnabledOnOs
 * @see DisabledOnOs
 */
@API(status = STABLE, since = "5.1")
public enum OS {

	/**
	 * IBM AIX operating system.
	 *
	 * @since 5.3
	 */
	@API(status = STABLE, since = "5.3")
	AIX,

	/**
	 * Linux-based operating system.
	 */
	LINUX,

	/**
	 * Apple Macintosh operating system (e.g., macOS).
	 */
	MAC,

	/**
	 * Oracle Solaris operating system.
	 */
	SOLARIS,

	/**
	 * Microsoft Windows operating system.
	 */
	WINDOWS,

	/**
	 * An operating system other than {@link #AIX}, {@link #LINUX}, {@link #MAC},
	 * {@link #SOLARIS}, or {@link #WINDOWS}.
	 */
	OTHER;

	private static final Logger logger = LoggerFactory.getLogger(OS.class);

	private static final OS CURRENT_OS = determineCurrentOs();

	private static OS determineCurrentOs() {
		return parse(System.getProperty("os.name"));
	}

	static OS parse(String osName) {
		if (StringUtils.isBlank(osName)) {
			logger.debug(
				() -> "JVM system property 'os.name' is undefined. It is therefore not possible to detect the current OS.");

			// null signals that the current OS is "unknown"
			return null;
		}

		osName = osName.toLowerCase(Locale.ENGLISH);

		if (osName.contains("aix")) {
			return AIX;
		}
		if (osName.contains("linux")) {
			return LINUX;
		}
		if (osName.contains("mac")) {
			return MAC;
		}
		if (osName.contains("sunos") || osName.contains("solaris")) {
			return SOLARIS;
		}
		if (osName.contains("win")) {
			return WINDOWS;
		}
		return OTHER;
	}

	/**
	 * @return {@code true} if <em>this</em> {@code OS} is known to be the
	 * operating system on which the current JVM is executing
	 */
	public boolean isCurrentOs() {
		return this == CURRENT_OS;
	}

}
