package edu.mit.csail.sdg.translator;

import java.util.Optional;

import kodkod.engine.satlab.SATFactory;

public class KKTransformer extends SATFactory {

    private static final long serialVersionUID = 1L;

    @Override
    public String id() {
        return "KK";
    }


    @Override
    public String type() {
        return "transformer";
    }

    @Override
    public String name() {
        return "KodKod output";
    }

    @Override
    public Optional<String> getDescription() {
        return Optional.of("KK is the KodKod debug output format");
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
