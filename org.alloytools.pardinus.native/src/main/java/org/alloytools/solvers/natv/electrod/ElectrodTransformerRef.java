package org.alloytools.solvers.natv.electrod;

import java.util.Optional;

import aQute.bnd.annotation.spi.ServiceProvider;
import kodkod.engine.satlab.SATFactory;

@ServiceProvider(SATFactory.class )
public class ElectrodTransformerRef extends ElectrodRef {

    private static final long serialVersionUID = 1L;


    public ElectrodTransformerRef() {
        super(null);
    }

    @Override
    public String id() {
        return "electrod.elo";
    }


    @Override
    public Optional<String> getDescription() {
        return Optional.ofNullable("outputs the elo file generated for electrod");
    }

    @Override
    public boolean isPresent() {
        return electrod != null;
    }

    @Override
    public String[] getExecutables() {
        return new String[] {
                             "electrod"
        };
    }

    @Override
    public boolean isTransformer() {
        return true;
    }

    @Override
    public String type() {
        return "transformer";
    }

    @Override
    public String name() {
        return "Electrod elo output";
    }

}
