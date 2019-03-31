package org.alloytools.alloy.solver.glucose.natve;

import org.alloytools.alloy.classic.solver.kodkod.AbstractKodkodSolver;
import org.alloytools.alloy.classic.solver.kodkod.KodkodOptions;
import org.alloytools.alloy.core.api.Alloy;
import org.alloytools.alloy.core.api.SolverType;

import kodkod.engine.satlab.Glucose;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.satlab.SATSolver;

public class GlucosePlugin extends AbstractKodkodSolver {

    public GlucosePlugin(Alloy core) {
        super(core);
    }

    @Override
    public String getId() {
        return "glucose(jni)";
    }

    @Override
    public SolverType getSolverType() {
        return SolverType.SAT;
    }

    @Override
    public String getName() {
        return "Glucose";
    }

    @Override
    public String getDescription() {
        return "Glucose is based on a new scoring scheme (well, not so new now, it was introduced in 2009) for the clause learning mechanism of so called \"Modern\" SAT sovlers (it is based our IJCAI'09 paper). It is designed to be parallel, since 2014. ";
    }

    @Override
    protected SATFactory getSATFactory(KodkodOptions options) {
        return new SATFactory() {

            @Override
            public SATSolver instance() {
                return new Glucose();
            }

            @Override
            public String toString() {
                return "Glucose";
            }
        };
    }

}
