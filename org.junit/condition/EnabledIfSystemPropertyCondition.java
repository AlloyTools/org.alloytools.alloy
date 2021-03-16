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

import static java.lang.String.format;
import static org.junit.jupiter.api.extension.ConditionEvaluationResult.disabled;
import static org.junit.jupiter.api.extension.ConditionEvaluationResult.enabled;

import org.junit.jupiter.api.extension.ConditionEvaluationResult;
import org.junit.jupiter.api.extension.ExecutionCondition;
import org.junit.platform.commons.util.Preconditions;

/**
 * {@link ExecutionCondition} for {@link EnabledIfSystemProperty @EnabledIfSystemProperty}.
 *
 * @since 5.1
 * @see EnabledIfSystemProperty
 */
class EnabledIfSystemPropertyCondition extends AbstractRepeatableAnnotationCondition<EnabledIfSystemProperty> {

	private static final ConditionEvaluationResult ENABLED = ConditionEvaluationResult.enabled(
		"No @EnabledIfSystemProperty conditions resulting in 'disabled' execution encountered");

	EnabledIfSystemPropertyCondition() {
		super(EnabledIfSystemProperty.class);
	}

	@Override
	protected ConditionEvaluationResult getNoDisabledConditionsEncounteredResult() {
		return ENABLED;
	}

	@Override
	protected ConditionEvaluationResult evaluate(EnabledIfSystemProperty annotation) {

		String name = annotation.named().trim();
		String regex = annotation.matches();
		Preconditions.notBlank(name, () -> "The 'named' attribute must not be blank in " + annotation);
		Preconditions.notBlank(regex, () -> "The 'matches' attribute must not be blank in " + annotation);
		String actual = System.getProperty(name);

		// Nothing to match against?
		if (actual == null) {
			return disabled(format("System property [%s] does not exist", name), annotation.disabledReason());
		}
		if (actual.matches(regex)) {
			return enabled(
				format("System property [%s] with value [%s] matches regular expression [%s]", name, actual, regex));
		}
		return disabled(
			format("System property [%s] with value [%s] does not match regular expression [%s]", name, actual, regex),
			annotation.disabledReason());
	}

}
