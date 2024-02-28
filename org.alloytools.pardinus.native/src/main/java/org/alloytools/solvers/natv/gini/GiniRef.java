package org.alloytools.solvers.natv.gini;

import java.util.Optional;

import kodkod.engine.satlab.ExternalSolver;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.satlab.SATSolver;

public class GiniRef extends SATFactory {

    private static final long serialVersionUID = 1L;

    @Override
    public String id() {
        return "gini";
    }

    @Override
    public String[] getExecutables() {
        return new String[] {
                             "gini"
        };
    }

    @Override
    public String toString() {
        return id();
    }

    @Override
    public SATSolver instance() {
        return new ExternalSolver("gini", null, true, "-model");
    }

    @Override
    public Optional<String> getDescription() {
        return Optional.of("The Gini sat solver is a fast, clean SAT solver written in Go. It is to our knowledge the first ever performant pure-Go SAT solver made available.\n" + "This solver is fully open source, originally developped at IRI France.");
    }

    @Override
    public String type() {
        return "external";
    }

}
