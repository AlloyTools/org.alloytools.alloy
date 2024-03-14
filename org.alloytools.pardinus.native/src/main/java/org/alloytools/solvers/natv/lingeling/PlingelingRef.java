package org.alloytools.solvers.natv.lingeling;

import java.util.Optional;

import aQute.bnd.annotation.spi.ServiceProvider;
import kodkod.engine.satlab.ExternalSolver;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.satlab.SATSolver;

@ServiceProvider(SATFactory.class )
public class PlingelingRef extends SATFactory {

    private static final long serialVersionUID = 1L;

    @Override
    public String id() {
        return "lingeling.parallel";
    }


    @Override
    public String[] getExecutables() {
        return new String[] {
                             "plingeling"
        };
    }

    @Override
    public Optional<String> getDescription() {
        return Optional.of("Plingeling is a parallel SAT solver that's part of the Lingeling family of SAT solvers developed by Armin Biere at Johannes Kepler University. SAT, or Boolean satisfiability, is the problem of determining if there exists an interpretation that satisfies a given Boolean formula.\n" + "Plingeling is designed to make efficient use of multiple processors or cores to solve SAT problems faster than a single-threaded solver would be able to. It does this by running several instances of the Lingeling solver in parallel, each working on the same problem but with different heuristics or random seed values.\n" + "Plingeling also incorporates techniques to share learned clauses between the different solver instances, which can help to avoid duplicate work and accelerate the overall solving process.\n");
    }

    @Override
    public String toString() {
        return id();
    }

    /**
     * Returns a SATFactory that produces SATSolver wrappers for Armin Biere's
     * Plingeling solver. This is a parallel solver that is invoked as an external
     * program rather than via the Java Native Interface. As a result, it cannot be
     * used incrementally. Its external factory manages the creation and deletion of
     * temporary files automatically. A statically compiled version of plingeling is
     * assumed to be available in a java.library.path directory.
     *
     * <p>
     * Plingeling takes as input two optional parameters: {@code threads},
     * specifying how many worker threads to use, and {@code portfolio}, specifying
     * whether the threads should run in portfolio mode (no sharing of clauses) or
     * sharing mode. If {@code threads} is null, the solver uses one worker per
     * core. If {@code portfolio} is null, it is set to true by default.
     * </p>
     *
     * @requires threads != null => numberOfThreads > 0
     *
     * @return SATFactory that produces SATSolver wrappers for the Plingeling solver
     */
    @Override
    public SATSolver instance() {
        return new ExternalSolver("plingeling", null, false);

    }

    @Override
    public String type() {
        return "external";
    }

}
