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

import static org.apiguardian.api.API.Status.STABLE;

import java.lang.annotation.Annotation;
import java.lang.reflect.Executable;
import java.lang.reflect.Parameter;
import java.util.List;
import java.util.Optional;

import org.apiguardian.api.API;

/**
 * {@code ParameterContext} encapsulates the <em>context</em> in which an
 * {@link #getDeclaringExecutable Executable} will be invoked for a given
 * {@link #getParameter Parameter}.
 *
 * <p>A {@code ParameterContext} is used to support parameter resolution via
 * a {@link ParameterResolver}.
 *
 * @since 5.0
 * @see ParameterResolver
 * @see java.lang.reflect.Parameter
 * @see java.lang.reflect.Executable
 * @see java.lang.reflect.Method
 * @see java.lang.reflect.Constructor
 */
@API(status = STABLE, since = "5.0")
public interface ParameterContext {

	/**
	 * Get the {@link Parameter} for this context.
	 *
	 * <h3>WARNING</h3>
	 * <p>When searching for annotations on the parameter in this context,
	 * favor {@link #isAnnotated(Class)}, {@link #findAnnotation(Class)}, and
	 * {@link #findRepeatableAnnotations(Class)} over methods in the
	 * {@link Parameter} API due to a bug in {@code javac} on JDK versions prior
	 * to JDK 9.
	 *
	 * @return the parameter; never {@code null}
	 * @see #getIndex()
	 */
	Parameter getParameter();

	/**
	 * Get the index of the {@link Parameter} for this context within the
	 * parameter list of the {@link #getDeclaringExecutable Executable} that
	 * declares the parameter.
	 *
	 * @return the index of the parameter
	 * @see #getParameter()
	 * @see Executable#getParameters()
	 */
	int getIndex();

	/**
	 * Get the {@link Executable} (i.e., the {@link java.lang.reflect.Method} or
	 * {@link java.lang.reflect.Constructor}) that declares the {@code Parameter}
	 * for this context.
	 *
	 * @return the declaring {@code Executable}; never {@code null}
	 * @see Parameter#getDeclaringExecutable()
	 */
	default Executable getDeclaringExecutable() {
		return getParameter().getDeclaringExecutable();
	}

	/**
	 * Get the target on which the {@link #getDeclaringExecutable Executable}
	 * that declares the {@link #getParameter Parameter} for this context will
	 * be invoked, if available.
	 *
	 * @return an {@link Optional} containing the target on which the
	 * {@code Executable} will be invoked; never {@code null} but will be
	 * <em>empty</em> if the {@code Executable} is a constructor or a
	 * {@code static} method.
	 */
	Optional<Object> getTarget();

	/**
	 * Determine if an annotation of {@code annotationType} is either
	 * <em>present</em> or <em>meta-present</em> on the {@link Parameter} for
	 * this context.
	 *
	 * <h3>WARNING</h3>
	 * <p>Favor the use of this method over directly invoking
	 * {@link Parameter#isAnnotationPresent(Class)} due to a bug in {@code javac}
	 * on JDK versions prior to JDK 9.
	 *
	 * @param annotationType the annotation type to search for; never {@code null}
	 * @return {@code true} if the annotation is present or meta-present
	 * @since 5.1.1
	 * @see #findAnnotation(Class)
	 * @see #findRepeatableAnnotations(Class)
	 */
	boolean isAnnotated(Class<? extends Annotation> annotationType);

	/**
	 * Find the first annotation of {@code annotationType} that is either
	 * <em>present</em> or <em>meta-present</em> on the {@link Parameter} for
	 * this context.
	 *
	 * <h3>WARNING</h3>
	 * <p>Favor the use of this method over directly invoking annotation lookup
	 * methods in the {@link Parameter} API due to a bug in {@code javac} on JDK
	 * versions prior to JDK 9.
	 *
	 * @param <A> the annotation type
	 * @param annotationType the annotation type to search for; never {@code null}
	 * @return an {@code Optional} containing the annotation; never {@code null} but
	 * potentially empty
	 * @since 5.1.1
	 * @see #isAnnotated(Class)
	 * @see #findRepeatableAnnotations(Class)
	 */
	<A extends Annotation> Optional<A> findAnnotation(Class<A> annotationType);

	/**
	 * Find all <em>repeatable</em> {@linkplain Annotation annotations} of
	 * {@code annotationType} that are either <em>present</em> or
	 * <em>meta-present</em> on the {@link Parameter} for this context.
	 *
	 * <h3>WARNING</h3>
	 * <p>Favor the use of this method over directly invoking annotation lookup
	 * methods in the {@link Parameter} API due to a bug in {@code javac} on JDK
	 * versions prior to JDK 9.
	 *
	 * @param <A> the annotation type
	 * @param annotationType the repeatable annotation type to search for; never
	 * {@code null}
	 * @return the list of all such annotations found; neither {@code null} nor
	 * mutable, but potentially empty
	 * @since 5.1.1
	 * @see #isAnnotated(Class)
	 * @see #findAnnotation(Class)
	 * @see java.lang.annotation.Repeatable
	 */
	<A extends Annotation> List<A> findRepeatableAnnotations(Class<A> annotationType);

}
