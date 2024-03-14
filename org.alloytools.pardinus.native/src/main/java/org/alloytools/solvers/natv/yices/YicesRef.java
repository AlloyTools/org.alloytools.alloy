package org.alloytools.solvers.natv.yices;

import aQute.bnd.annotation.spi.ServiceProvider;
import kodkod.engine.satlab.SATFactory;

@ServiceProvider(SATFactory.class )
public class YicesRef extends SATFactory {

    private static final long serialVersionUID = 1L;

    @Override
    public String id() {
        return "yices";
    }

    @Override
    public String[] getLibraries() {
        return new String[] {
                             "yices"
        };
    }

    @Override
    public Yices instance() {
        return new Yices();
    }

    @Override
    public boolean incremental() {
        return true;
    }

    // TOOD is this maxsat? since external is?

    @Override
    public boolean maxsat() {
        return true;
    }

    @Override
    public String type() {
        return "jni";
    }

}
