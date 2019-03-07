package org.alloytools.alloy.solver.lingeling.natve;

import org.alloytools.alloy.classic.solver.kodkod.AbstractKodkodSolver;
import org.alloytools.alloy.classic.solver.kodkod.KodkodOptions;
import org.alloytools.alloy.core.api.Alloy;
import org.alloytools.alloy.core.api.SolverType;

import kodkod.engine.satlab.Lingeling;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.satlab.SATSolver;

public class LingelingPlugin extends AbstractKodkodSolver {

    public LingelingPlugin(Alloy core) {
        super(core);
    }

    @Override
    public String getId() {
        return "lingeling(jni)";
    }

    @Override
    public SolverType getSolverType() {
        return SolverType.SAT;
    }

    @Override
    public String getName() {
        return "Lingeling";
    }

    @Override
    public String getDescription() {
        return "Lingeling";
    }

    @Override
    protected SATFactory getSATFactory(KodkodOptions options) {
        return new SATFactory() {

            @Override
            public SATSolver instance() {
                return new Lingeling();
            }

            @Override
            public boolean incremental() {
                return false;
            }

            @Override
            public String toString() {
                return getName();
            }
        };
    }

}
