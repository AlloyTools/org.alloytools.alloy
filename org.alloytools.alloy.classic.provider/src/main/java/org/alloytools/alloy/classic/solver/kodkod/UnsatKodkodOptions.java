package org.alloytools.alloy.classic.solver.kodkod;

@Description("Options for the Unsat facility of Kodkod")
public class UnsatKodkodOptions extends KodkodOptions {

	@Description("Unsat core granularity, " + "default is 0 (only top-level conjuncts are considered), "
		+ "3 expands all quantifiers")
	public int	coreGranularity		= 0;

	public int	coreMinimization	= 0;
}
