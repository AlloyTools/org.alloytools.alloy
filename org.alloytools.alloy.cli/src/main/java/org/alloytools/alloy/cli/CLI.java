package org.alloytools.alloy.cli;

import java.io.IOException;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.alloytools.alloy.cli.CLI.CLIOptions.CoreMininmization;
import org.alloytools.alloy.cli.CLI.CLIOptions.DecomposeStrategy;
import org.alloytools.alloy.infrastructure.api.AlloyMain;

import aQute.lib.collections.ExtList;
import aQute.lib.env.Env;
import aQute.lib.getopt.Arguments;
import aQute.lib.getopt.CommandLine;
import aQute.lib.getopt.Description;
import aQute.lib.getopt.Options;
import aQute.lib.justif.Justif;
import aQute.libg.glob.Glob;
import edu.mit.csail.sdg.alloy4.SafeList;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Options.SatSolver;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

@AlloyMain(name = { "shell", "exec" })
public class CLI extends Env {
	final CommandLine	cl		= new CommandLine(this);
	final A4Options		options	= new A4Options();

	public interface CLIOptions extends aQute.lib.getopt.Options {
		/**
		 * default true
		 */
		@Description("Infer partial instances (??). Default true")
		boolean inferPartialInstance(boolean dflt);

		/**
		 * This option specifies the amount of symmetry breaking to do (when
		 * symmetry breaking isn't explicitly disabled).
		 * <p>
		 * If a formula is unsatisfiable, then in general, the higher this
		 * value, the faster you finish the solving. But if this value is too
		 * high, it will instead slow down the solving.
		 * <p>
		 * If a formula is satisfiable, then in general, the lower this value,
		 * the faster you finish the solving. Setting this value to 0 usually
		 * gives the fastest solve.
		 * <p>
		 * Default value is 20.
		 */
		@Description("Amount of symmetry breaking to do when symmetry breaking isn't explicitly disabled. If a formula is "
				+ "unsatisfiable, then in general, the higher this value, the "
				+ "faster the solver is finished. But if this value is too high, it will instead slow down the solving. Default is 20")
		int breakingSymmetry(int deflt);

		/**
		 * This option specifies the maximum skolem-function depth.
		 * <p>
		 * Default value is 0, which means it will only generate skolem
		 * constants, and will not generate skolem functions.
		 */
		@Description("Maximum skolem-function depth. Default value is 0, which means it will only generate skolem constants, and will not generate skolem functions.")
		int skolemDepth(int deflt);

		enum CoreMininmization {
			GuaranteedLocalMinimum, FasterButLessAccurate, EventFaster
		}

		/**
		 * This option specifies the unsat core minimization strategy
		 * (0=GuaranteedLocalMinimum 1=FasterButLessAccurate 2=EvenFaster...)
		 * <p>
		 * Default value is set to the fastest current strategy.
		 */
		@Description("This option specifies the unsat core minimization strategy (GuaranteedLocalMinimum,FasterButLessAccurate,EvenFaster). Default value is set to the fastest current strategy.")
		CoreMininmization coreMinimization(CoreMininmization deflt);

		/**
		 * This option specifies the SAT solver to use (SAT4J, MiniSatJNI,
		 * MiniSatProverJNI, ZChaffJNI...)
		 * <p>
		 * Default value is SAT4J.
		 */
		@Description("The solver to use. Use `alloy solvers` to list all available solvers. Default is SAT4J")
		String solver(String deflt);

		/**
		 * This option specifies whether the solver should report only solutions
		 * that don't cause any overflows.
		 */
		@Description("Whether the solver should report only solutions that don't cause any overflows.")
		boolean noOverflow(boolean deflt);

		/**
		 * This option controls how deep we unroll loops and unroll recursive
		 * predicate/function/macros (negative means it's disallowed). Default
		 * is disallowed.
		 */
		@Description("How deep we unroll loops and unroll recursive predicate/function/macros (negative means it's disallowed). Default is -1 (disallowed).")
		int recurse(int deflt);

		enum DecomposeStrategy {
			Off, Hybrid, Parallel
		}

		/**
		 * This option specifies the decompose strategy (0=Off 1=Hybrid
		 * 2=Parallel)
		 * <p>
		 * Default value is off.
		 */
		@Description("This option specifies the decompose strategy (Off,Hybrid,Parallel). Default value is Off.")
		DecomposeStrategy decompose_mode(DecomposeStrategy dflt);

		/**
		 * This option specifies the number of threads when following a
		 * decompose strategy
		 * <p>
		 * Default value is 4.
		 */
		@Description("This option specifies the number of threads when following a decompose strategy. Default value is 4.")
		int decompose_threads(int deflt);

		/**
		 * Set trace level
		 */

		boolean trace();

		/**
		 * Set exceptions
		 */

		boolean exceptions();
	}

	public void __run(CLIOptions options) throws Exception {

		if (options.trace()) {
			setTrace(true);
		}
		if (options.exceptions()) {
			setExceptions(true);
		}
		this.options.coreMinimization = options
				.coreMinimization(CoreMininmization.values()[this.options.coreMinimization]).ordinal();
		this.options.decompose_mode = options.decompose_mode(DecomposeStrategy.values()[this.options.decompose_mode])
				.ordinal();
		this.options.decompose_threads = options.decompose_threads(this.options.decompose_threads);
		this.options.inferPartialInstance = options.inferPartialInstance(this.options.inferPartialInstance);
		this.options.noOverflow = options.noOverflow(this.options.noOverflow);
		this.options.skolemDepth = options.skolemDepth(this.options.skolemDepth);
		String solver = options.solver(this.options.solver.id());
		this.options.solver = SatSolver.parse(solver);
		if (!this.options.solver.id().equals(solver)) {
			warning("The solver name %s not found, using %s. Use `alloy solvers` to see a list of all solvers",
					solver, this.options.solver);
		}
		this.options.symmetry = options.breakingSymmetry(this.options.symmetry);
		this.options.unrolls = options.recurse(this.options.unrolls);

		List<String> args = options._arguments();
		if (args.isEmpty()) {
			Justif j = new Justif();
			cl.help(j.formatter(), this);
			System.out.println(j.wrap());
			return;
		}

		String help = cl.execute(this, args.remove(0), args);
		if (help != null) {
			System.out.println(help);
		}
		report(System.out);

	}

	/**
	 * Show the list of solvers
	 */

	@Arguments(arg = {})
	@Description("Show the list of solvers")
	interface SolverOptions extends Options {
		@Description("Show extended information")
		boolean xtended();
	}

	public void _solvers(SolverOptions options) {
		SafeList<SatSolver> values = SatSolver.values();
		values.forEach(s -> {
			if (options.xtended()) {
				System.out.printf("%-20s %-20s %s\n", s.id(), maskNull(s.external()), Arrays.toString(s.options()));
			} else {
				System.out.println(s.id());
			}
		});

	}

	private String maskNull(Object s) {
		if (s == null) {
			return "";
		}
		return s.toString();
	}

	/**
	 * Run all 'run' & asserts
	 */

	@Arguments(arg = "path")
	interface ExecOptions extends Options {
		String command();
	}

	public void _exec(ExecOptions options) throws IOException {
		SimpleReporter rep = new SimpleReporter(this);

		String filename = options._arguments().remove(0);
		System.out.println("exec " + filename);
		
		Map<String, String> cache = new HashMap<>();
		Module world = CompUtil.parseEverything_fromFile(rep, cache, filename);

		Glob glob;
		if (options.command() != null) {
			glob = new Glob(options.command());
		} else
			glob = Glob.ALL;

		for (Command c : world.getAllCommands()) {
			
			if (!glob.matches(c.label)) {
				continue;
			}

			System.out.format("Command %s\n", c);

			A4Solution s = TranslateAlloyToKodkod.execute_commandFromBook(rep, world.getAllReachableSigs(), c,
					this.options);

			int n = 0;
			while (s.satisfiable()) {
				
				String format = s.format();
				System.out.println(format);
				System.out.println("-----------------"+n+"------------------");
				if (s.isIncremental()) {
					s = s.next();
				} else
					break;
				n++;
			}
		}

	}

	public void _shell(Shell.ShellOptions options) throws Exception {
		String filename = options._arguments().remove(0);
		try (Shell s = new Shell(this, getFile(filename), options)) {
			s.loop();
		}
	}

	public static void main(String[] args) throws Exception {
		CLI cli = new CLI();
		List<String> list = new ExtList<>(args);
		cli.cl.execute(cli, "_run", list);
	}
}
