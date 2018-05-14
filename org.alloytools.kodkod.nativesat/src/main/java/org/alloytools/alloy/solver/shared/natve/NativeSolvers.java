package org.alloytools.alloy.solver.shared.natve;

import java.util.HashSet;
import java.util.Set;

import org.alloytools.alloy.core.api.Alloy;
import org.alloytools.alloy.solver.api.AlloySolver;
import org.alloytools.alloy.solver.api.AlloySolverFactory;
import org.alloytools.alloy.solver.glucose.natve.GlucosePlugin;
import org.alloytools.alloy.solver.lingeling.natve.LingelingPlugin;
import org.alloytools.alloy.solver.minisat.natve.MiniSatPlugin;
import org.alloytools.alloy.solver.minisat.natve.MiniSatProverPlugin;
import org.alloytools.alloy.solver.plingeling.natve.PlingelingPlugin;

public class NativeSolvers implements AlloySolverFactory {

    @Override
    public Set<AlloySolver> getAvailableSolvers(Alloy core) {
        Set<AlloySolver> solvers = new HashSet<>();
        ifAvailable(solvers, new GlucosePlugin(core));
        ifAvailable(solvers, new LingelingPlugin(core));
        ifAvailable(solvers, new MiniSatProverPlugin(core));
        ifAvailable(solvers, new MiniSatPlugin(core));
        ifAvailable(solvers, new PlingelingPlugin(core));
        return solvers;
    }

    private void ifAvailable(Set<AlloySolver> solvers, AlloySolver solver) {
        if (solver.isAvailable())
            solvers.add(solver);
    }

}
