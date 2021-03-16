/*
 * Copyright 2015-2021 the original author or authors.
 *
 * All rights reserved. This program and the accompanying materials are
 * made available under the terms of the Eclipse Public License v2.0 which
 * accompanies this distribution and is available at
 *
 * https://www.eclipse.org/legal/epl-v20.html
 */

package org.junit.jupiter.api.extension;

import static java.util.Collections.emptyList;
import static org.apiguardian.api.API.Status.STABLE;

import java.util.List;

import org.apiguardian.api.API;

/**
 * {@code TestTemplateInvocationContext} represents the <em>context</em> of a
 * single invocation of a {@linkplain org.junit.jupiter.api.TestTemplate test
 * template}.
 *
 * <p>Each context is provided by a {@link TestTemplateInvocationContextProvider}.
 *
 * @since 5.0
 * @see org.junit.jupiter.api.TestTemplate
 * @see TestTemplateInvocationContextProvider
 */
@API(status = STABLE, since = "5.0")
public interface TestTemplateInvocationContext {

	/**
	 * Get the display name for this invocation.
	 *
	 * <p>The supplied {@code invocationIndex} is incremented by the framework
	 * with each test invocation. Thus, in the case of multiple active
	 * {@linkplain TestTemplateInvocationContextProvider providers}, only the
	 * first active provider receives indices starting with {@code 1}.
	 *
	 * <p>The default implementation returns the supplied {@code invocationIndex}
	 * wrapped in brackets &mdash; for example, {@code [1]}, {@code [42]}, etc.
	 *
	 * @param invocationIndex the index of this invocation (1-based).
	 * @return the display name for this invocation; never {@code null} or blank
	 */
	default String getDisplayName(int invocationIndex) {
		return "[" + invocationIndex + "]";
	}

	/**
	 * Get the additional {@linkplain Extension extensions} for this invocation.
	 *
	 * <p>The extensions provided by this method will only be used for this
	 * invocation of the test template. Thus, it does not make sense to return
	 * an extension that acts solely on the container level (e.g.
	 * {@link BeforeAllCallback}).
	 *
	 * <p>The default implementation returns an empty list.
	 *
	 * @return the additional extensions for this invocation; never {@code null}
	 * or containing {@code null} elements, but potentially empty
	 */
	default List<Extension> getAdditionalExtensions() {
		return emptyList();
	}

}
