package org.alloytools.solvers.natv.lingeling;

import java.util.Optional;

import kodkod.engine.satlab.SATFactory;
import kodkod.engine.satlab.SATSolver;

public class LingelingRef extends SATFactory {

    private static final long serialVersionUID = 1L;

    @Override
    public String id() {
        return "lingeling";
    }

    @Override
    public SATSolver instance() {
        return new Lingeling();
    }

    @Override
    public boolean incremental() {
        return true;
    }


    @Override
    public String[] getLibraries() {
        return new String[] {
                             "lingeling"
        };
    }

    @Override
    public Optional<String> getDescription() {
        return Optional.of("Lingeling is an efficient, open-source SAT solver developed by Armin Biere at Johannes Kepler University in Linz, Austria." + "Lingeling is designed to handle large and complex SAT instances and has been successful in numerous SAT competitions, often outperforming many other solvers. It employs a variety of algorithmic techniques, including conflict-driven clause learning, clause elimination, and preprocessing, among others.");
    }

    @Override
    public String type() {
        return "jni";
    }

}
