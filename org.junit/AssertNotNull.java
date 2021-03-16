/*
 * Copyright 2015-2021 the original author or authors.
 *
 * All rights reserved. This program and the accompanying materials are
 * made available under the terms of the Eclipse Public License v2.0 which
 * accompanies this distribution and is available at
 *
 * https://www.eclipse.org/legal/epl-v20.html
 */

package org.junit.jupiter.api;

import static org.junit.jupiter.api.AssertionUtils.buildPrefix;
import static org.junit.jupiter.api.AssertionUtils.nullSafeGet;

import java.util.function.Supplier;

/**
 * {@code AssertNotNull} is a collection of utility methods that support asserting
 * that there is an object.
 *
 * @since 5.0
 */
class AssertNotNull {

	private AssertNotNull() {
		/* no-op */
	}

	static void assertNotNull(Object actual) {
		assertNotNull(actual, (String) null);
	}

	static void assertNotNull(Object actual, String message) {
		if (actual == null) {
			failNull(message);
		}
	}

	static void assertNotNull(Object actual, Supplier<String> messageSupplier) {
		if (actual == null) {
			failNull(nullSafeGet(messageSupplier));
		}
	}

	private static void failNull(String message) {
		Assertions.fail(buildPrefix(message) + "expected: not <null>");
	}
}
