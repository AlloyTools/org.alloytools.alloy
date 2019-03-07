package org.alloytools.alloy.classic.solver.kodkod;

import org.alloytools.alloy.core.api.SolverOptions;

@Description("Options for the Kodkod solver")
public class KodkodOptions extends SolverOptions {

	@Description("?")
	public boolean	inferPartialInstance	= false;

	// TODO remove?
	@Description("This option specifies whether the solver should report only solutions that\n"
		+ "don't cause any overflows.")
	public boolean	noOverflow				= false;

	@Description("This option specifies whether the compiler should record the original Kodkod\n"
		+ "formula being generated and the resulting Kodkod instances.")
	public boolean	recordKodkod			= false;

	@Description("This option specifies the maximum skolem-function depth.\n"
		+ "Default value is 0, which means it will only generate skolem constants, and\n"
		+ "will not generate skolem functions.\n")
	public int		skolemDepth				= 0;

	@Description("This option specifies the amount of symmetry breaking to do (when symmetry\n"
		+ "breaking isn't explicitly disabled).\n"
		+ "If a formula is unsatisfiable, then in general, the higher this value, the\n"
		+ "faster you finish the solving. But if this value is too high, it will instead\n" + "slow down the solving.\n"
		+ "If a formula is satisfiable, then in general, the lower this value, the\n"
		+ "faster you finish the solving. Setting this value to 0 usually gives the\n" + "fastest solve.\n")
	public int		symmetry				= 20;

	@Description("This option constrols how deep we unroll loops and unroll recursive\n"
		+ "predicate/function/macros (negative means it's disallowed)")
	public int		unrolls					= 3;

}
