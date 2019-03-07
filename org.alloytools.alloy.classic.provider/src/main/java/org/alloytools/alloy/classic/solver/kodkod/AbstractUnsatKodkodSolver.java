package org.alloytools.alloy.classic.solver.kodkod;

import org.alloytools.alloy.core.api.Alloy;
import org.alloytools.alloy.core.api.SolverOptions;

import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import kodkod.engine.Solver;

public abstract class AbstractUnsatKodkodSolver extends AbstractKodkodSolver {

	public AbstractUnsatKodkodSolver(Alloy core) {
		super(core);
	}

	@Override
	public SolverOptions newOptions() {
		return new UnsatKodkodOptions();
	}

	protected void setOptions(A4Options classic, SolverOptions modern) {
		super.setOptions(classic, modern);
		UnsatKodkodOptions m = (UnsatKodkodOptions) modern;
		classic.coreGranularity = m.coreGranularity;
		classic.coreMinimization = m.coreMinimization;
	}

	@Override
	protected void setup(KodkodOptions options, A4Solution solution) {
		super.setup(options, solution);
		UnsatKodkodOptions unsat = (UnsatKodkodOptions) options;
		Solver solver = solution.getSolver();
		solver.options()
			.setLogTranslation(2);
		solver.options()
			.setCoreGranularity(unsat.coreGranularity);
		// TODO unsat.coreMinimization?
	}

}
