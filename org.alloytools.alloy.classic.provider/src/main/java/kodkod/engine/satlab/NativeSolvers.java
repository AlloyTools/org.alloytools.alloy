package kodkod.engine.satlab;

import java.util.HashSet;
import java.util.Set;

import org.alloytools.alloy.core.api.Alloy;
import org.alloytools.alloy.core.api.Solver;
import org.alloytools.alloy.core.spi.AlloySolverFactory;

public class NativeSolvers implements AlloySolverFactory {

	@Override
	public Set<Solver> getAvailableSolvers(Alloy core) {
		Set<Solver> solvers = new HashSet<>();
		solvers.add(new GlucosePlugin(core));
		solvers.add(new LingelingPlugin(core));
		solvers.add(new MiniSatProverPlugin(core));
		solvers.add(new MiniSatPlugin(core));
		solvers.add(new PlingelingPlugin(core));
		return solvers;
	}

}
