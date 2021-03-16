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

import static java.util.Comparator.comparingInt;
import static org.apiguardian.api.API.Status.EXPERIMENTAL;

import java.util.Collections;
import java.util.Comparator;
import java.util.Optional;

import org.apiguardian.api.API;
import org.junit.platform.commons.logging.Logger;
import org.junit.platform.commons.logging.LoggerFactory;

/**
 * {@code ClassOrderer} defines the API for ordering the <em>top-level test
 * classes</em>, without considering nested test classes.
 *
 * <p>In this context, the term "test class" refers to any class containing methods
 * annotated with {@code @Test}, {@code @RepeatedTest}, {@code @ParameterizedTest},
 * {@code @TestFactory}, or {@code @TestTemplate}. {@link Nested @Nested} test
 * classes cannot be ordered by a {@code ClassOrderer}.
 *
 * <h4>Built-in Implementations</h4>
 *
 * <p>JUnit Jupiter provides the following built-in {@code ClassOrderer}
 * implementations.
 *
 * <ul>
 * <li>{@link ClassOrderer.ClassName}</li>
 * <li>{@link ClassOrderer.DisplayName}</li>
 * <li>{@link ClassOrderer.OrderAnnotation}</li>
 * <li>{@link ClassOrderer.Random}</li>
 * </ul>
 *
 * @since 5.8
 * @see ClassOrdererContext
 * @see #orderClasses(ClassOrdererContext)
 */
@API(status = EXPERIMENTAL, since = "5.8")
public interface ClassOrderer {

	/**
	 * Order the classes encapsulated in the supplied {@link ClassOrdererContext}.
	 *
	 * <p>The classes to order or sort are made indirectly available via
	 * {@link ClassOrdererContext#getClassDescriptors()}. Since this method
	 * has a {@code void} return type, the list of class descriptors must be
	 * modified directly.
	 *
	 * <p>For example, a simplified implementation of the {@link ClassOrderer.Random}
	 * {@code ClassOrderer} might look like the following.
	 *
	 * <pre class="code">
	 * public void orderClasses(ClassOrdererContext context) {
	 *     Collections.shuffle(context.getClassDescriptors());
	 * }
	 * </pre>
	 *
	 * @param context the {@code ClassOrdererContext} containing the
	 * {@linkplain ClassDescriptor class descriptors} to order; never {@code null}
	 */
	void orderClasses(ClassOrdererContext context);

	/**
	 * {@code ClassOrderer} that sorts classes alphanumerically based on their
	 * fully qualified names using {@link String#compareTo(String)}.
	 */
	class ClassName implements ClassOrderer {

		public ClassName() {
		}

		/**
		 * Sort the classes encapsulated in the supplied
		 * {@link ClassOrdererContext} alphanumerically based on their fully
		 * qualified names.
		 */
		@Override
		public void orderClasses(ClassOrdererContext context) {
			context.getClassDescriptors().sort(comparator);
		}

		private static final Comparator<ClassDescriptor> comparator = Comparator.comparing(
			descriptor -> descriptor.getTestClass().getName());
	}

	/**
	 * {@code ClassOrderer} that sorts classes alphanumerically based on their
	 * display names using {@link String#compareTo(String)}
	 */
	class DisplayName implements ClassOrderer {

		public DisplayName() {
		}

		/**
		 * Sort the classes encapsulated in the supplied
		 * {@link ClassOrdererContext} alphanumerically based on their display
		 * names.
		 */
		@Override
		public void orderClasses(ClassOrdererContext context) {
			context.getClassDescriptors().sort(comparator);
		}

		private static final Comparator<ClassDescriptor> comparator = Comparator.comparing(
			ClassDescriptor::getDisplayName);
	}

	/**
	 * {@code ClassOrderer} that sorts classes based on the {@link Order @Order}
	 * annotation.
	 *
	 * <p>Any classes that are assigned the same order value will be sorted
	 * arbitrarily adjacent to each other.
	 *
	 * <p>Any classes not annotated with {@code @Order} will be assigned the
	 * {@link Order#DEFAULT default order} value which will effectively cause them
	 * to appear at the end of the sorted list, unless certain classes are assigned
	 * an explicit order value greater than the default order value. Any classes
	 * assigned an explicit order value greater than the default order value will
	 * appear after non-annotated classes in the sorted list.
	 */
	class OrderAnnotation implements ClassOrderer {

		public OrderAnnotation() {
		}

		/**
		 * Sort the classes encapsulated in the supplied
		 * {@link ClassOrdererContext} based on the {@link Order @Order}
		 * annotation.
		 */
		@Override
		public void orderClasses(ClassOrdererContext context) {
			context.getClassDescriptors().sort(comparingInt(OrderAnnotation::getOrder));
		}

		private static int getOrder(ClassDescriptor descriptor) {
			return descriptor.findAnnotation(Order.class).map(Order::value).orElse(Order.DEFAULT);
		}
	}

	/**
	 * {@code ClassOrderer} that orders classes pseudo-randomly.
	 *
	 * <h4>Custom Seed</h4>
	 *
	 * <p>By default, the random <em>seed</em> used for ordering classes is the
	 * value returned by {@link System#nanoTime()} during static initialization
	 * of this class. In order to support repeatable builds, the value of the
	 * default random seed is logged at {@code INFO} level. In addition, a
	 * custom seed (potentially the default seed from the previous test plan
	 * execution) may be specified via the {@link Random#RANDOM_SEED_PROPERTY_NAME
	 * junit.jupiter.execution.class.order.random.seed} <em>configuration parameter</em>
	 * which can be supplied via the {@code Launcher} API, build tools (e.g.,
	 * Gradle and Maven), a JVM system property, or the JUnit Platform configuration
	 * file (i.e., a file named {@code junit-platform.properties} in the root of
	 * the class path). Consult the User Guide for further information.
	 *
	 * @see Random#RANDOM_SEED_PROPERTY_NAME
	 * @see java.util.Random
	 */
	class Random implements ClassOrderer {

		private static final Logger logger = LoggerFactory.getLogger(Random.class);

		/**
		 * Default seed, which is generated during initialization of this class
		 * via {@link System#nanoTime()} for reproducibility of tests.
		 */
		private static final long DEFAULT_SEED;

		static {
			DEFAULT_SEED = System.nanoTime();
			logger.info(() -> "ClassOrderer.Random default seed: " + DEFAULT_SEED);
		}

		/**
		 * Property name used to set the random seed used by this
		 * {@code ClassOrderer}: {@value}
		 *
		 * <p>The same property is used by {@link MethodOrderer.Random} for
		 * consistency between the two random orderers.
		 *
		 * <h3>Supported Values</h3>
		 *
		 * <p>Supported values include any string that can be converted to a
		 * {@link Long} via {@link Long#valueOf(String)}.
		 *
		 * <p>If not specified or if the specified value cannot be converted to
		 * a {@link Long}, the default random seed will be used (see the
		 * {@linkplain Random class-level Javadoc} for details).
		 *
		 * @see MethodOrderer.Random
		 */
		public static final String RANDOM_SEED_PROPERTY_NAME = MethodOrderer.Random.RANDOM_SEED_PROPERTY_NAME;

		public Random() {
		}

		/**
		 * Order the classes encapsulated in the supplied
		 * {@link ClassOrdererContext} pseudo-randomly.
		 */
		@Override
		public void orderClasses(ClassOrdererContext context) {
			Collections.shuffle(context.getClassDescriptors(),
				new java.util.Random(getCustomSeed(context).orElse(DEFAULT_SEED)));
		}

		private Optional<Long> getCustomSeed(ClassOrdererContext context) {
			return context.getConfigurationParameter(RANDOM_SEED_PROPERTY_NAME).map(configurationParameter -> {
				Long seed = null;
				try {
					seed = Long.valueOf(configurationParameter);
					logger.config(
						() -> String.format("Using custom seed for configuration parameter [%s] with value [%s].",
							RANDOM_SEED_PROPERTY_NAME, configurationParameter));
				}
				catch (NumberFormatException ex) {
					logger.warn(ex,
						() -> String.format(
							"Failed to convert configuration parameter [%s] with value [%s] to a long. "
									+ "Using default seed [%s] as fallback.",
							RANDOM_SEED_PROPERTY_NAME, configurationParameter, DEFAULT_SEED));
				}
				return seed;
			});
		}
	}

}
