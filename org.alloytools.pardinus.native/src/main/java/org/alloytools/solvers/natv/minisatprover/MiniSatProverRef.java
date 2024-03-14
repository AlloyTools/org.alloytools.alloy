package org.alloytools.solvers.natv.minisatprover;

import aQute.bnd.annotation.spi.ServiceProvider;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.satlab.SATSolver;

@ServiceProvider(SATFactory.class )
public class MiniSatProverRef extends SATFactory {

    private static final long serialVersionUID = 1L;


    @Override
    public String id() {
        return "minisat.prover";
    }

    @Override
    public MiniSatProverRef doOptions(ExtendedOptions options) {
        options.setLogTranslation(2);
        options.setSymmetryBreaking(20);
        return this;
    }

    @Override
    public SATSolver instance() {
        return new MiniSatProver();
    }


    @Override
    public boolean incremental() {
        return true;
    }


    @Override
    public boolean prover() {
        return true;
    }


    @Override
    public String[] getLibraries() {
        return new String[] {
                             "minisatprover"
        };
    }

    @Override
    public String toString() {
        return id();
    }

    @Override
    public String type() {
        return "jni";
    }


}
