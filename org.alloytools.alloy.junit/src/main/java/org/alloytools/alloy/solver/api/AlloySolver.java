package org.alloytools.alloy.solver.api;

import org.alloytools.alloy.core.api.AlloyModule;
import org.alloytools.alloy.core.api.Check;
import org.alloytools.alloy.core.api.Command;

public interface AlloySolver {
	SolverType getSolverType();

	String getName();

	String getDescription();

	AlloySolution run(AlloyModule module, Command command);
	AlloySolution check(AlloyModule module, Check command);

}
