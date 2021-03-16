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
import static org.junit.jupiter.api.AssertionUtils.fail;
import static org.junit.jupiter.api.AssertionUtils.format;
import static org.junit.jupiter.api.AssertionUtils.nullSafeGet;

import java.util.function.Supplier;

/**
 * {@code AssertNull} is a collection of utility methods that support asserting
 * there is no object.
 *
 * @since 5.0
 */
class AssertNull {

	private AssertNull() {
		/* no-op */
	}

	static void assertNull(Object actual) {
		assertNull(actual, (String) null);
	}

	static void assertNull(Object actual, String message) {
		if (actual != null) {
			failNotNull(actual, message);
		}
	}

	static void assertNull(Object actual, Supplier<String> messageSupplier) {
		if (actual != null) {
			failNotNull(actual, nullSafeGet(messageSupplier));
		}
	}

	private static void failNotNull(Object actual, String message) {
		String stringRepresentation = actual.toString();
		if (stringRepresentation == null || stringRepresentation.equals("null")) {
			fail(format(null, actual, message), null, actual);
		}
		else {
			fail(buildPrefix(message) + "expected: <null> but was: <" + actual + ">", null, actual);
		}
	}

}
