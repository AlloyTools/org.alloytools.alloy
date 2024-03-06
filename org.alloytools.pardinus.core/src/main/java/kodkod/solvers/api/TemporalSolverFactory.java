package kodkod.solvers.api;

import kodkod.engine.TemporalSolver;
import kodkod.engine.config.ExtendedOptions;

public interface TemporalSolverFactory {
	TemporalSolver<ExtendedOptions> getTemporalSolver(ExtendedOptions options);
}
