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

import static org.apiguardian.api.API.Status.STABLE;

import java.lang.annotation.Documented;
import java.lang.annotation.ElementType;
import java.lang.annotation.Inherited;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

import org.apiguardian.api.API;

/**
 * {@code @TestInstance} is a type-level annotation that is used to configure
 * the {@linkplain Lifecycle lifecycle} of test instances for the annotated
 * test class or test interface.
 *
 * <p>If {@code @TestInstance} is not explicitly declared on a test class or
 * on a test interface implemented by a test class, the lifecycle mode will
 * implicitly default to {@link Lifecycle#PER_METHOD PER_METHOD}. Note, however,
 * that an explicit lifecycle mode is <em>inherited</em> within a test class
 * hierarchy. In addition, the <em>default</em> lifecycle mode may be overridden
 * via the {@code junit.jupiter.testinstance.lifecycle.default} <em>configuration
 * parameter</em> which can be supplied via the {@code Launcher} API, build tools
 * (e.g., Gradle and Maven), a JVM system property, or the JUnit Platform
 * configuration file (i.e., a file named {@code junit-platform.properties} in
 * the root of the class path). Consult the User Guide for further information.
 *
 * <h3>Use Cases</h3>
 * <p>Setting the test instance lifecycle mode to {@link Lifecycle#PER_CLASS
 * PER_CLASS} enables the following features.
 * <ul>
 * <li>Shared test instance state between test methods in a given test class
 * as well as between non-static {@link BeforeAll @BeforeAll} and
 * {@link AfterAll @AfterAll} methods in the test class.</li>
 * <li>Declaration of {@link BeforeAll @BeforeAll} and {@link AfterAll @AfterAll}
 * methods in {@link Nested @Nested} test classes.</li>
 * <li>Declaration of {@link BeforeAll @BeforeAll} and {@link AfterAll @AfterAll}
 * on interface {@code default} methods.</li>
 * <li>Simplified declaration of {@link BeforeAll @BeforeAll} and
 * {@link AfterAll @AfterAll} methods in test classes implemented with the Kotlin
 * programming language.</li>
 * </ul>
 *
 * <p>{@code @TestInstance} may also be used as a meta-annotation in order to
 * create a custom <em>composed annotation</em> that inherits the semantics
 * of {@code @TestInstance}.
 *
 * @since 5.0
 * @see Nested @Nested
 */
@Target(ElementType.TYPE)
@Retention(RetentionPolicy.RUNTIME)
@Inherited
@Documented
@API(status = STABLE, since = "5.0")
public @interface TestInstance {

	/**
	 * Enumeration of test instance lifecycle <em>modes</em>.
	 *
	 * @see #PER_METHOD
	 * @see #PER_CLASS
	 */
	enum Lifecycle {

		/**
		 * When using this mode, a new test instance will be created once per test class.
		 *
		 * @see #PER_METHOD
		 */
		PER_CLASS,

		/**
		 * When using this mode, a new test instance will be created for each test method,
		 * test factory method, or test template method.
		 *
		 * <p>This mode is analogous to the behavior found in JUnit versions 1 through 4.
		 *
		 * @see #PER_CLASS
		 */
		PER_METHOD;

	}

	/**
	 * The test instance lifecycle <em>mode</em> to use.
	 */
	Lifecycle value();

}
