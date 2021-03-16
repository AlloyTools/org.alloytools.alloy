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
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

import org.apiguardian.api.API;

/**
 * {@code @AfterEach} is used to signal that the annotated method should be
 * executed <em>after</em> <strong>each</strong> {@code @Test},
 * {@code @RepeatedTest}, {@code @ParameterizedTest}, {@code @TestFactory},
 * and {@code @TestTemplate} method in the current test class.
 *
 * <h3>Method Signatures</h3>
 *
 * <p>{@code @AfterEach} methods must have a {@code void} return type,
 * must not be {@code private}, and must not be {@code static}.
 * They may optionally declare parameters to be resolved by
 * {@link org.junit.jupiter.api.extension.ParameterResolver ParameterResolvers}.
 *
 * <h3>Inheritance and Execution Order</h3>
 *
 * <p>{@code @AfterEach} methods are inherited from superclasses as long as
 * they are not overridden. Furthermore, {@code @AfterEach} methods from
 * superclasses will be executed after {@code @AfterEach} methods in subclasses.
 *
 * <p>Similarly, {@code @AfterEach} methods declared as <em>interface default
 * methods</em> are inherited as long as they are not overridden, and
 * {@code @AfterEach} default methods will be executed after {@code @AfterEach}
 * methods in the class that implements the interface.
 *
 * <p>JUnit Jupiter does not guarantee the execution order of multiple
 * {@code @AfterEach} methods that are declared within a single test class or
 * test interface. While it may at times appear that these methods are invoked
 * in alphabetical order, they are in fact sorted using an algorithm that is
 * deterministic but intentionally non-obvious.
 *
 * <p>In addition, {@code @AfterEach} methods are in no way linked to
 * {@code @BeforeEach} methods. Consequently, there are no guarantees with
 * regard to their <em>wrapping</em> behavior. For example, given two
 * {@code @BeforeEach} methods {@code createA()} and {@code createB()} as well
 * as two {@code @AfterEach} methods {@code destroyA()} and {@code destroyB()},
 * the order in which the {@code @BeforeEach} methods are executed (e.g.
 * {@code createA()} before {@code createB()}) does not imply any order for the
 * seemingly corresponding {@code @AfterEach} methods. In other words,
 * {@code destroyA()} might be called before <em>or</em> after
 * {@code destroyB()}. The JUnit Team therefore recommends that developers
 * declare at most one {@code @BeforeEach} method and at most one
 * {@code @AfterEach} method per test class or test interface unless there are
 * no dependencies between the {@code @BeforeEach} methods or between the
 * {@code @AfterEach} methods.
 *
 * <h3>Composition</h3>
 *
 * <p>{@code @AfterEach} may be used as a meta-annotation in order to create
 * a custom <em>composed annotation</em> that inherits the semantics of
 * {@code @AfterEach}.
 *
 * @since 5.0
 * @see BeforeEach
 * @see BeforeAll
 * @see AfterAll
 * @see Test
 * @see RepeatedTest
 * @see TestFactory
 * @see TestTemplate
 */
@Target({ ElementType.ANNOTATION_TYPE, ElementType.METHOD })
@Retention(RetentionPolicy.RUNTIME)
@Documented
@API(status = STABLE, since = "5.0")
public @interface AfterEach {
}
