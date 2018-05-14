package org.alloytools.alloy.solver.api;

import java.util.Set;

import org.alloytools.alloy.core.api.Alloy;

public interface AlloySolverFactory {

	Set<AlloySolver> getAvailableSolvers(Alloy alloy);
}
