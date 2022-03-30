package kodkod.engine.satlab;

import org.alloytools.alloy.classic.solver.kodkod.AbstractKodkodSolver;
import org.alloytools.alloy.classic.solver.kodkod.KodkodOptions;
import org.alloytools.alloy.core.api.Alloy;
import org.alloytools.alloy.core.api.SolverType;
import org.alloytools.alloy.infrastructure.api.AlloySolver;

@AlloySolver(
             name = LingelingPlugin.NAME )
public class LingelingPlugin extends AbstractKodkodSolver {

    final static String NAME = "lingeling";

	public LingelingPlugin(Alloy core) {
		super(core);
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
		return "Lingeling";
	}

	@Override
	public String getDescription() {
		return "Lingeling";
	}

	@Override
	protected SATFactory getSATFactory(KodkodOptions options) {
		return new SATFactory() {

			@Override
			public SATSolver instance() {
				return new Lingeling();
			}

			@Override
			public boolean incremental() {
				return false;
			}

			@Override
			public String toString() {
				return getName();
			}
		};
	}

}
