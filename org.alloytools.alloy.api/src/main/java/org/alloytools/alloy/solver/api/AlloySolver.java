package org.alloytools.alloy.solver.api;

import org.alloytools.alloy.core.api.AlloyModule;
import org.alloytools.alloy.core.api.TCheck;
import org.alloytools.alloy.core.api.TRun;

public interface AlloySolver {
	
	String getId();
	
	boolean isAvailable();
	
	SolverType getSolverType();

	String getName();

	String getDescription();

	Class<? extends AlloyOptions> getOptionsType();
	
	AlloySolution run(AlloyModule module, AlloyOptions options, TRun command);

	AlloySolution check(AlloyModule module, AlloyOptions options, TCheck command);
}
