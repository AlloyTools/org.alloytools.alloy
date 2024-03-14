package org.alloytools.solvers.natv.yices;

import aQute.bnd.annotation.spi.ServiceProvider;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.satlab.WTargetSATSolver;

@ServiceProvider(SATFactory.class )
public class YicesExternalRef extends SATFactory {

    private static final long serialVersionUID = 1L;

    @Override
    public String id() {
        return "yices.external";
    }

    @Override
    public String[] getExecutables() {
        return new String[] {
                             "yices"
        };
    }

    @Override
    public WTargetSATSolver instance() {
        return new PMaxYicesExternal("yices", null, false, 2000, "-d", "-e", "-ms", "-mw", "" + 2000);
    }



    @Override
    public boolean maxsat() {
        return true;
    }

    @Override
    public String type() {
        return "jni";
    }

}
