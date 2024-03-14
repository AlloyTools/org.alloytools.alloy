package edu.mit.csail.sdg.translator;

import java.util.Optional;

import kodkod.engine.satlab.SATFactory;

public class CNFTransformer extends SATFactory {

    private static final long serialVersionUID = 1L;

    @Override
    public String id() {
        return "CNF";
    }

    @Override
    public String name() {
        return "CNF output";
    }

    @Override
    public Optional<String> getDescription() {
        return Optional.of("CNF stands for Conjunctive Normal Form. It is specified by DIMACS. This is a standardized way of representing Boolean algebra expressions for processing by SAT solvers.");
    }

    @Override
    public String type() {
        return "transformer";
    }

    @Override
    public boolean isTransformer() {
        return true;
    }

    @Override
    public boolean isPresent() {
        return true;
    }
}
