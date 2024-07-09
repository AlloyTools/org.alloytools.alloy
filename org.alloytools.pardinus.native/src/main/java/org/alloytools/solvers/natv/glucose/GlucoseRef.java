package org.alloytools.solvers.natv.glucose;

import java.util.Optional;

import aQute.bnd.annotation.spi.ServiceProvider;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.satlab.SATSolver;

@ServiceProvider(SATFactory.class )
public class GlucoseRef extends SATFactory {

    private static final long serialVersionUID = 1L;


    @Override
    public String id() {
        return "glucose";
    }

    @Override
    public String[] getLibraries() {
        return isWindows ? new String[] {
                                         "msvcrt", "libwinpthread-1", "libgcc_s_seh-1", "libstdc++-6", "glucose"
        } : new String[] {
                          "glucose"
        };
    }

    @Override
    public boolean incremental() {
        return true;
    }

    @Override
    public Optional<String> getDescription() {
        return Optional.of("Glucose is an efficient and open-source SAT solver based on the MiniSat solver. It was developed by Gilles Audemard and Laurent Simon.\n" + "The name \"Glucose\" comes from adding some \"glue clauses\" to the MiniSat, which refers to a specific kind of learned clause (the ones that are considered important and are kept during the clause database reduction process). The use of glue clauses has shown to be particularly effective for hard industrial SAT instances.\n" + "Glucose incorporates an approach called \"Literal Block Distance\" (LBD) to measure the 'activity' of learned clauses. The LBD measure helps in making decisions about which clauses to keep when the memory becomes full. This mechanism makes Glucose more efficient in dealing with large and complex problems.");
    }

    @Override
    public SATSolver instance() {
        return new Glucose();
    }

    @Override
    public String type() {
        return "jni";
    }

}
