package org.alloytools.kodkod.sat4j;

import org.alloytools.alloy.classic.solver.kodkod.AbstractKodkodSolver;
import org.alloytools.alloy.classic.solver.kodkod.KodkodOptions;
import org.alloytools.alloy.core.api.Alloy;
import org.alloytools.alloy.core.api.SolverType;
import org.alloytools.alloy.infrastructure.api.AlloySolver;
import org.sat4j.minisat.SolverFactory;

import kodkod.engine.satlab.SATFactory;
import kodkod.engine.satlab.SATSolver;

@AlloySolver(
             name = SAT4JPlugin.NAME )
public class SAT4JPlugin extends AbstractKodkodSolver {

    final static String NAME = "sat4j";
    public SAT4JPlugin(Alloy core) {
        super(core);
    }

    @Override
    public String getId() {
        return NAME;
    }

    @Override
    public SolverType getSolverType() {
        return SolverType.SAT;
    }

    @Override
    public String getName() {
        return "SAT4J";
    }

    @Override
    public String getDescription() {
        return "Sat4j is a full featured boolean reasoning library designed to bring state-of-the-art SAT technologies to the Java Virtual Machine.";
    }

    @Override
    protected SATFactory getSATFactory(KodkodOptions options) {
        return new SATFactory() {

            @Override
            public SATSolver instance() {
                return new SAT4J(SolverFactory.instance().defaultSolver());
            }

            @Override
            public String toString() {
                return "DefaultSAT4J";
            }
        };
    }

    @Override
    public boolean isJavaOnly() {
        return true;
    }

}
