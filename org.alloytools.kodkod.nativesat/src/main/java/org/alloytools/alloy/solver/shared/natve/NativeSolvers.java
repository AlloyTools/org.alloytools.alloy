package org.alloytools.alloy.solver.shared.natve;

import java.util.HashSet;
import java.util.Set;

import org.alloytools.alloy.core.api.Alloy;
import org.alloytools.alloy.core.api.Solver;
import org.alloytools.alloy.core.spi.AlloySolverFactory;
import org.alloytools.alloy.solver.glucose.natve.GlucosePlugin;
import org.alloytools.alloy.solver.lingeling.natve.LingelingPlugin;
import org.alloytools.alloy.solver.minisat.natve.MiniSatPlugin;
import org.alloytools.alloy.solver.minisat.natve.MiniSatProverPlugin;
import org.alloytools.alloy.solver.plingeling.natve.PlingelingPlugin;

public class NativeSolvers implements AlloySolverFactory {

    @Override
    public Set<Solver> getAvailableSolvers(Alloy core) {
        Set<Solver> solvers = new HashSet<>();
        ifAvailable(solvers, new GlucosePlugin(core));
        ifAvailable(solvers, new LingelingPlugin(core));
        ifAvailable(solvers, new MiniSatProverPlugin(core));
        ifAvailable(solvers, new MiniSatPlugin(core));
        ifAvailable(solvers, new PlingelingPlugin(core));
        return solvers;
    }

    private void ifAvailable(Set<Solver> solvers, Solver solver) {
        if (solver.isAvailable())
            solvers.add(solver);
    }

}
