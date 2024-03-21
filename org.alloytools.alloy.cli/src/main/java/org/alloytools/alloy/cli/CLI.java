package org.alloytools.alloy.cli;

import java.io.File;
import java.io.FileOutputStream;
import java.io.FilterInputStream;
import java.io.FilterOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.PrintStream;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.TreeMap;
import java.util.concurrent.TimeUnit;
import java.util.function.Predicate;

import org.alloytools.alloy.dto.SolutionDTO;
import org.alloytools.alloy.infrastructure.api.AlloyMain;

import aQute.lib.env.Env;
import aQute.lib.getopt.Arguments;
import aQute.lib.getopt.Description;
import aQute.lib.getopt.Options;
import aQute.lib.io.IO;
import aQute.lib.json.JSONCodec;
import aQute.libg.glob.Glob;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.A4SolutionWriter;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;
import kodkod.engine.satlab.SATFactory;

/**
 * 
 * @author aqute
 *
 */
@AlloyMain
public class CLI extends Env {
	final A4Options options = new A4Options();

	public enum OutputType {
		none, text, table, json, xml;
	}

	InputStream stdin = new FilterInputStream(System.in) {
		@Override
		public void close() throws IOException {
		}
	};
	PrintStream stdout = new PrintStream(new FilterOutputStream(System.out)) {
		public void close() {
			System.out.flush();
		};
	};

	/**
	 * Show the list of solvers
	 */

	/**
	 * Run all 'run' & asserts
	 */

	@Arguments(arg = "path")
	@Description("Execute an Alloy program")
	interface ExecOptions extends Options {
		@Description("The command to run. If no command is specified, the default command will run. The command may specify wildcards to run multiple commands. If the command is an integer, it will run the command with that index.")
		String command();

		@Description("Specify the output type: plain, json, xml, or none")
		OutputType type(OutputType deflt);

		@Description("Specify where the output should go. Default is the console")
		String output();

		@Description("If set, the solution will include only those models in which no arithmetic overflows occur")
		boolean nooverflow();

		@Description("Number of allowed recursion unrolls. Default is 0")
		int unrolls(int n);

		@Description("Depth for skolem analysis, default is 0")
		int depth(int n);

		@Description("Symmetry breaking removes instances that are symmetric to other instances. The parameter indicates the amount of effort Alloy can spend. The default is 20.")
		int ymmetry(int n);

		@Description("Set the solver to use. You can get a list of solver names with the 'solvers' command. The default solver is SAT4J.")
		String solver(String solver);

		@Description("Be quiet with progress information")
		boolean quiet();

		@Description("After resolving each command, start an evaluator")
		boolean evaluator();

		@Description("Find multiple solutions, up to this number. Use 0 for as many as can be found.")
		int repeat(int deflt);

	}

	/**
	 * Execute a Alloy program
	 * 
	 * @param options the options to use
	 */
	@Description("Execute an Alloy program")
	public void _exec(ExecOptions options) throws Exception {

		SimpleReporter rep = new SimpleReporter(this);
		A4Options opt = this.options.dup();
		opt.noOverflow = options.nooverflow();
		opt.unrolls = options.unrolls(opt.unrolls);
		opt.skolemDepth = options.depth(opt.skolemDepth);
		opt.symmetry = options.depth(opt.symmetry);

		Optional<SATFactory> solver = SATFactory.find(options.solver("sat4j"));
		if (!solver.isPresent()) {
			error("No such solver %s. Use the `solvers` command to see the available solvers", options.solver(null));
			return;
		}
		opt.solver = solver.get();

		String filename = options._arguments().remove(0);
		File file = IO.getFile(filename);
		if (!file.isFile()) {
			error("No such file %s", file);
			return;
		}
		if (!file.canRead()) {
			error("Cannot read file %s", file);
			return;
		}

		Map<String, String> cache = new HashMap<>();
		CompModule world = CompUtil.parseEverything_fromFile(rep, cache, filename);

		List<Command> commands = world.getAllCommands();

		String cmd = options.command();
		Predicate<Command> run;
		if (cmd == null) {
			run = c -> true;
		} else if (cmd.matches("[0-9]+")) {
			int index = Integer.parseInt(cmd);
			if (index >= commands.size()) {
				error("command index %s is more than available commands %s", index, commands);
			}
			run = c -> commands.indexOf(c) == index;
		} else {
			Glob g = new Glob(cmd);
			run = c -> g.matches(c.label);
		}

		OutputStream out = output(options.output());
		if (out == null) {
			return;
		}

		Map<CommandInfo, A4Solution> answers = new TreeMap<>();
		for (Command c : commands) {
			if (!run.test(c)) {
				trace("ignore command %s", c);
				continue;
			}

			if (!options.quiet())
				stdout.println("solving command " + c);

			long start = System.nanoTime();
			A4Solution s = TranslateAlloyToKodkod.execute_commandFromBook(rep, world.getAllReachableSigs(), c, opt);
			long finish = System.nanoTime();
			int repeat = options.repeat(-1);
			if (repeat == 0) {
				repeat = Integer.MAX_VALUE;
			}
			if (s.satisfiable()) {
				int sequence = 0;
				do {
					repeat--;
					System.out.println("repeat " + repeat);
					CommandInfo info = new CommandInfo();
					info.command = c;
					info.sequence = sequence++;
					info.durationInMs = TimeUnit.NANOSECONDS.toMillis(finish - start);
					if (opt.solver.isTransformer())
						info.cnf = rep.output;
					answers.put(info, s);
					System.out.println("answers " + answers.size());
				} while (repeat >= 0 && s.isIncremental() && (s = s.next()).satisfiable());
			}
		}
		if (!options.quiet() && answers.isEmpty()) {
			stdout.println("no commands found " + cmd);
		}

		if (opt.solver.isTransformer()) {
			for (CommandInfo c : answers.keySet()) {
				IO.copy(c.cnf, out);
			}

		} else {
			generate(world, answers, options.type(OutputType.table), out);

			if (options.evaluator() && !answers.isEmpty()) {
				evaluator(world, answers);
			}
		}
	}

	private void evaluator(CompModule world, Map<CommandInfo, A4Solution> answers) throws Exception {
		for (Entry<CommandInfo, A4Solution> s : answers.entrySet()) {
			A4Solution sol = s.getValue();
			if (sol.satisfiable()) {
				stdout.println("Evaluator for " + s.getKey().command);
				stdout.flush();
				Evaluator e = new Evaluator(world, sol, stdin, stdout);
				String lastCommand = e.loop();
				if (lastCommand.equals("/exit"))
					break;
			}
		}
		stdout.println("bye");
	}

	@Arguments(arg = "path")
	@Description("List the commands in an alloy file")
	interface CommandsOptions extends Options {

	}

	/**
	 * Execute a Alloy program
	 * 
	 * @param options the options to use
	 */
	@Description("Show all commands in an Alloy program")
	public void _commands(CommandsOptions options) throws Exception {
		SimpleReporter rep = new SimpleReporter(this);
		String filename = options._arguments().remove(0);
		Map<String, String> cache = new HashMap<>();
		CompModule world = CompUtil.parseEverything_fromFile(rep, cache, filename);
		int n = 0;
		for (Command c : world.getAllCommands()) {
			stdout.printf("%-2d. %s%n", n++, c);
		}
	}

	private OutputStream output(String output) throws IOException {

		if (output == null) {
			return stdout;
		}

		File file = IO.getFile(output);
		file.getParentFile().mkdirs();
		if (!file.getParentFile().isDirectory()) {
			error("Cannot create parent directory for %s", file);
			return null;
		}
		return new FileOutputStream(file);
	}

	private void generate(CompModule world, Map<CommandInfo, A4Solution> s, OutputType type, OutputStream out)
			throws Exception {
		try {
			switch (type) {
			default:
			case none:
				return;

			case text:
				try (PrintWriter pw = new PrintWriter(out)) {
					for (Map.Entry<CommandInfo, A4Solution> e : s.entrySet()) {
						A4Solution solution = e.getValue();
						CommandInfo cmdinfo = e.getKey();
						pw.println(cmdinfo);
						pw.println(solution.toString());
					}
				}
				return;

			case table:
				try (PrintWriter pw = new PrintWriter(out)) {
					for (Map.Entry<CommandInfo, A4Solution> e : s.entrySet()) {
						A4Solution solution = e.getValue();
						CommandInfo cmdinfo = e.getKey();
						
						pw.println("---");
						pw.printf("%-40s%s%n", "Command", cmdinfo.command);
						pw.printf("%-40s%s%n", "Duration (ms)", cmdinfo.durationInMs);
						pw.printf("%-40s%s%n", "Sequence", cmdinfo.sequence);
						for ( ExprVar expr : solution.getAllSkolems()) {
							Object eval = solution.eval(expr);
							pw.printf("%-40s%s%n", expr.label, eval);
							
						}
						pw.println(e.getValue().toTable());
					}
				}
				break;

			case json:
				List<SolutionDTO> trace = new ArrayList<>();

				for (Map.Entry<CommandInfo, A4Solution> e : s.entrySet()) {
					A4Solution a4s = e.getValue();
					a4s.setModule(world);
					trace.add(a4s.toDTO());
				}
				JSONCodec codec = new JSONCodec();
				codec.enc().writeDefaults().indent("  ").to(out).put(trace);
				break;

			case xml:
				try (PrintWriter pw = new PrintWriter(out)) {
					if (s.size() > 1) {
						pw.println("<top>");
					}
					for (Map.Entry<CommandInfo, A4Solution> e : s.entrySet()) {
						A4SolutionWriter.writeInstance(null, e.getValue(), pw, Collections.emptyList(),
								Collections.emptyMap());
					}
					if (s.size() > 1) {
						pw.println("</top>");
					}
				}
				break;

			}
		} finally {
			IO.close(out);
		}
	}

	@Override
	public String toString() {
		return "CLI";
	}
}
