/*
 * Copyright 2015-2021 the original author or authors.
 *
 * All rights reserved. This program and the accompanying materials are
 * made available under the terms of the Eclipse Public License v2.0 which
 * accompanies this distribution and is available at
 *
 * https://www.eclipse.org/legal/epl-v20.html
 */

package org.junit.jupiter.api.parallel;

import static org.apiguardian.api.API.Status.EXPERIMENTAL;

import java.lang.annotation.ElementType;
import java.lang.annotation.Inherited;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

import org.apiguardian.api.API;

/**
 * {@code @Execution} is used to configure the parallel execution
 * {@linkplain #value mode} of a test class or test method.
 *
 * <p>Since JUnit Jupiter 5.4, this annotation is {@linkplain Inherited inherited}
 * within class hierarchies.
 *
 * @see Isolated
 * @see ResourceLock
 * @since 5.3
 */
@API(status = EXPERIMENTAL, since = "5.3")
@Retention(RetentionPolicy.RUNTIME)
@Target({ ElementType.TYPE, ElementType.METHOD })
@Inherited
public @interface Execution {

	/**
	 * The required/preferred execution mode.
	 *
	 * @see ExecutionMode
	 */
	ExecutionMode value();

}
