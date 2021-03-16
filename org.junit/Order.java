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

import static org.apiguardian.api.API.Status.EXPERIMENTAL;

import java.lang.annotation.Documented;
import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

import org.apiguardian.api.API;

/**
 * {@code @Order} is an annotation that is used to configure the
 * {@linkplain #value order} in which the annotated element (i.e., field,
 * method, or class) should be evaluated or executed relative to other elements
 * of the same category.
 *
 * <p>When used with
 * {@link org.junit.jupiter.api.extension.RegisterExtension @RegisterExtension},
 * the category applies to <em>extension fields</em>. When used with
 * {@link MethodOrderer.OrderAnnotation}, the category applies to <em>test methods</em>.
 * When used with {@link ClassOrderer.OrderAnnotation}, the category applies to
 * top-level <em>test classes</em>.
 *
 * <p>If {@code @Order} is not explicitly declared on an element, the
 * {@link #DEFAULT} order value will be assigned to the element.
 *
 * @since 5.4
 * @see MethodOrderer.OrderAnnotation
 * @see ClassOrderer.OrderAnnotation
 * @see org.junit.jupiter.api.extension.RegisterExtension @RegisterExtension
 */
@Target({ ElementType.FIELD, ElementType.METHOD, ElementType.TYPE })
@Retention(RetentionPolicy.RUNTIME)
@Documented
@API(status = EXPERIMENTAL, since = "5.4")
public @interface Order {

	/**
	 * Default order value for elements not explicitly annotated with {@code @Order},
	 * equal to the value of {@code Integer.MAX_VALUE / 2}.
	 *
	 * @since 5.6
	 * @see Order#value
	 */
	@API(status = EXPERIMENTAL, since = "5.6")
	int DEFAULT = Integer.MAX_VALUE / 2;

	/**
	 * The order value for the annotated element (i.e., field, method, or class).
	 *
	 * <p>Elements are ordered based on priority where a lower value has greater
	 * priority than a higher value. For example, {@link Integer#MAX_VALUE} has
	 * the lowest priority.
	 *
	 * @see #DEFAULT
	 */
	int value();

}
