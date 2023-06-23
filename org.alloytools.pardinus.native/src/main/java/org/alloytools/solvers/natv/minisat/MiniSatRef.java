package org.alloytools.solvers.natv.minisat;

import java.util.Optional;

import kodkod.engine.satlab.SATFactory;
import kodkod.engine.satlab.SATSolver;

public class MiniSatRef extends SATFactory {

    private static final long serialVersionUID = 1L;

    @Override
    public String id() {
        return "minisat";
    }

    @Override
    public SATSolver instance() {
        return new MiniSat();
    }

    @Override
    public boolean incremental() {
        return true;
    }

    @Override
    public String[] getLibraries() {
        return new String[] {
                             "minisat"
        };
    }

    @Override
    public Optional<String> getDescription() {
        return Optional.of("MiniSat is a minimalistic, open-source SAT solver that is designed to be simple and efficient. It's written in C++ and is widely used in both academia and industry for research purposes and as a basis for derivative SAT solvers.");
    }

    @Override
    public String type() {
        return "jni";
    }

}
