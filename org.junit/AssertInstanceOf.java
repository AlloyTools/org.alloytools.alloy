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
import static org.junit.jupiter.api.AssertionUtils.format;
import static org.junit.jupiter.api.AssertionUtils.nullSafeGet;

import java.util.function.Supplier;

import org.opentest4j.AssertionFailedError;

/**
 * {@code AssertInstanceOf} is a collection of utility methods that support
 * asserting that an object is of an expected type &mdash; in other words, if it
 * can be assigned to the expected type.
 *
 * @since 5.8
 */
class AssertInstanceOf {

	private AssertInstanceOf() {
		/* no-op */
	}

	static <T> T assertInstanceOf(Class<T> expectedType, Object actualValue) {
		return assertInstanceOf(expectedType, actualValue, (Object) null);
	}

	static <T> T assertInstanceOf(Class<T> expectedType, Object actualValue, String message) {
		return assertInstanceOf(expectedType, actualValue, (Object) message);
	}

	static <T> T assertInstanceOf(Class<T> expectedType, Object actualValue, Supplier<String> messageSupplier) {
		return assertInstanceOf(expectedType, actualValue, (Object) messageSupplier);
	}

	private static <T> T assertInstanceOf(Class<T> expectedType, Object actualValue, Object messageOrSupplier) {
		if (!expectedType.isInstance(actualValue)) {
			String reason = (actualValue == null ? "Unexpected null value" : "Unexpected type");
			String message = buildPrefix(nullSafeGet(messageOrSupplier))
					+ format(expectedType, actualValue == null ? null : actualValue.getClass(), reason);
			throw new AssertionFailedError(message);
		}
		return expectedType.cast(actualValue);
	}

}
