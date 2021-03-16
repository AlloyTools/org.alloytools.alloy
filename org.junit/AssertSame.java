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

import static org.junit.jupiter.api.AssertionUtils.fail;
import static org.junit.jupiter.api.AssertionUtils.format;
import static org.junit.jupiter.api.AssertionUtils.nullSafeGet;

import java.util.function.Supplier;

/**
 * {@code AssertSame} is a collection of utility methods that support asserting
 * two objects are the same.
 *
 * @since 5.0
 */
class AssertSame {

	private AssertSame() {
		/* no-op */
	}

	static void assertSame(Object expected, Object actual) {
		assertSame(expected, actual, (String) null);
	}

	static void assertSame(Object expected, Object actual, String message) {
		if (expected != actual) {
			failNotSame(expected, actual, message);
		}
	}

	static void assertSame(Object expected, Object actual, Supplier<String> messageSupplier) {
		if (expected != actual) {
			failNotSame(expected, actual, nullSafeGet(messageSupplier));
		}
	}

	private static void failNotSame(Object expected, Object actual, String message) {
		fail(format(expected, actual, message), expected, actual);
	}

}
