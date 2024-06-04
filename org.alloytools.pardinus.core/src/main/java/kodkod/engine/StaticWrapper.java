package kodkod.engine;

import kodkod.ast.Formula;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.PardinusBounds;
import kodkod.solvers.api.TemporalSolverFactory;

public class StaticWrapper {
    public static AbstractSolver wrap(TemporalSolverFactory temporalFactory, ExtendedOptions options) {
        options.setMinTraceLength(1);
        options.setMaxTraceLength(1);
        options.setRunTemporal(true);
        TemporalSolver<ExtendedOptions> temporalSolver = temporalFactory.getTemporalSolver(options);
        return new AbstractSolver<PardinusBounds, ExtendedOptions>() {
            @Override
            public ExtendedOptions options() {
                return temporalSolver.options();
            }

            @Override
            public Solution solve(Formula formula, PardinusBounds bounds) {
                return temporalSolver.solve(formula, bounds);
            }
        };
    }
}
