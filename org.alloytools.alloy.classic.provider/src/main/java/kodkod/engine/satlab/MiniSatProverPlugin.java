package kodkod.engine.satlab;

import org.alloytools.alloy.classic.solver.kodkod.AbstractUnsatKodkodSolver;
import org.alloytools.alloy.classic.solver.kodkod.KodkodOptions;
import org.alloytools.alloy.core.api.Alloy;
import org.alloytools.alloy.core.api.SolverType;
import org.alloytools.alloy.infrastructure.api.AlloySolver;

@AlloySolver
public class MiniSatProverPlugin extends AbstractUnsatKodkodSolver {

	public MiniSatProverPlugin(Alloy core) {
		super(core);
	}

	@Override
	public String getId() {
		return "minisatprover(jni)";
	}

	@Override
	public SolverType getSolverType() {
		return SolverType.SAT_WITH_UNSAT_CORE;
	}

	@Override
	public String getName() {
		return "MiniSat with Unsat Core";
	}

	@Override
	public String getDescription() {
		return "MiniSat is a minimalistic, open-source SAT solver, developed to " //
				+ "help researchers and developers alike to get started on SAT.";
	}

	@Override
	protected SATFactory getSATFactory(KodkodOptions options) {
		return new SATFactory() {

			@Override
			public SATSolver instance() {
				return new MiniSatProver();
			}

			@Override
			public boolean prover() {
				return true;
			}

			@Override
			public String toString() {
				return getName();
			}
		};
	}

}
