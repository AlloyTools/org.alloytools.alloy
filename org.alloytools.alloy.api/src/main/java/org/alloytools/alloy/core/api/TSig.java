package org.alloytools.alloy.core.api;

import java.util.List;
import java.util.Optional;

public interface TSig {
	String getName();

	List<? extends TField> getFields();

	Optional<? extends TField> getTField(String fieldName);

	String getValuePattern();
}
