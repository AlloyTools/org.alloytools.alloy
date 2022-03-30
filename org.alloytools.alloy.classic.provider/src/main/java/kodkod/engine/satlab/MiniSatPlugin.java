package kodkod.engine.satlab;

import org.alloytools.alloy.classic.solver.kodkod.AbstractKodkodSolver;
import org.alloytools.alloy.classic.solver.kodkod.KodkodOptions;
import org.alloytools.alloy.core.api.Alloy;
import org.alloytools.alloy.core.api.SolverType;
import org.alloytools.alloy.infrastructure.api.AlloySolver;

@AlloySolver(
             name = MiniSatPlugin.NAME )
public class MiniSatPlugin extends AbstractKodkodSolver {

    final static String NAME = "minisat";

	public MiniSatPlugin(Alloy core) {
		super(core);
		// TODO Auto-generated constructor stub
	}

	@Override
	public String getId() {
        return NAME;
	}

	@Override
	public SolverType getSolverType() {
		return SolverType.SAT;
	}

	@Override
	public String getName() {
		return "MiniSat";
	}

	@Override
	public String getDescription() {
		return "MiniSat is a minimalistic, open-source SAT solver, developed to help researchers and developers alike to get started on SAT.";
	}

	@Override
	protected SATFactory getSATFactory(KodkodOptions options) {
		return new SATFactory() {

			@Override
			public SATSolver instance() {
				return new MiniSat();
			}

			@Override
			public String toString() {
				return getName();
			}
		};
	}

}
