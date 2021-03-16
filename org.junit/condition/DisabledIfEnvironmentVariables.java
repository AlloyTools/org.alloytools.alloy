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

import java.lang.annotation.Documented;
import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

import org.apiguardian.api.API;

/**
 * {@code @DisabledIfEnvironmentVariables} is a container for one or more
 * {@link DisabledIfEnvironmentVariable @DisabledIfEnvironmentVariable} declarations.
 *
 * <p>Note, however, that use of the {@code @DisabledIfEnvironmentVariables} container
 * is completely optional since {@code @DisabledIfEnvironmentVariable} is a {@linkplain
 * java.lang.annotation.Repeatable repeatable} annotation.
 *
 * @since 5.6
 * @see DisabledIfEnvironmentVariable
 * @see java.lang.annotation.Repeatable
 */
@Target({ ElementType.TYPE, ElementType.METHOD })
@Retention(RetentionPolicy.RUNTIME)
@Documented
@API(status = STABLE, since = "5.6")
public @interface DisabledIfEnvironmentVariables {

	/**
	 * An array of one or more {@link DisabledIfEnvironmentVariable @DisabledIfEnvironmentVariable}
	 * declarations.
	 */
	DisabledIfEnvironmentVariable[] value();

}
