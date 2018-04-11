package org.alloytools.alloy.solver.api;

import org.alloytools.alloy.core.api.AlloyModule;
import org.alloytools.alloy.core.api.TCheck;
import org.alloytools.alloy.core.api.TRun;

public interface AlloySolver {
	SolverType getSolverType();

	String getName();

	String getDescription();

	AlloySolution run(AlloyModule module, TRun command);

	AlloySolution check(AlloyModule module, TCheck command);

	AlloyOptions getOptions();
	void setOptions();
}
