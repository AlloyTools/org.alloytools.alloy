package org.alloytools.alloy.cli;

import java.io.File;
import java.io.FilterInputStream;
import java.io.FilterOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.PrintStream;
import java.io.PrintWriter;
import java.util.Collections;
import java.util.Formatter;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.TreeMap;
import java.util.concurrent.TimeUnit;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import org.alloytools.alloy.infrastructure.api.AlloyMain;
import org.alloytools.util.table.Table;

import aQute.bnd.exceptions.Exceptions;
import aQute.lib.env.Env;
import aQute.lib.getopt.Arguments;
import aQute.lib.getopt.Description;
import aQute.lib.getopt.Options;
import aQute.lib.io.IO;
import aQute.lib.json.JSONCodec;
import aQute.lib.strings.Strings;
import aQute.libg.glob.Glob;
import edu.mit.csail.sdg.alloy4.TableView;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.sim.SimTupleset;
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

		@Description("Specify the output type: none, text, table, json, xml")
		OutputType type(OutputType deflt);

		@Description("Specify where the output should go. Default is the console. If a name specified, this will become a directory with the different outputs ordered as separate file with meaningful command names.")
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
			error("No such solver %s: %s", options.solver(null),
					SATFactory.getSolvers().stream().map(sf -> sf.id()).collect(Collectors.joining(", ")));
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

		File outdir = output(options.output(), getStem(file));
		OutputTrace trace = new OutputTrace(options.quiet() ? null : stdout);
		Map<CommandInfo, A4Solution> answers = new TreeMap<>();
		int n = 0;
		for (Command c : commands) {
			if (!run.test(c)) {
				trace("ignore command %s", c);
				continue;
			}
			int repeat = options.repeat(1);
			if (repeat == 0) {
				repeat = Integer.MAX_VALUE;
			}
			int index = 0;
			trace.format("%02d. %-5s %-20s %-60s\n", n, c.check ? "check" : "run", c.label, c.scope);
			String cname = toCName(c) + "-" + n;

			try {
				A4Solution solution = TranslateAlloyToKodkod.execute_commandFromBook(rep, world.getAllReachableSigs(),
						c, opt);

				if (!solution.satisfiable()) {
					if (rep.output != null) {
						trace.format("  %s", cname + "." + ext(rep.output));
						showTransformerFile(rep.output, outdir, cname);
					} else {
						trace.format("UNSAT");
					}
				} else {
					int back = 0;
					do {
						if (repeat > 1)
							trace.back(back).format("repeat %-5d\n", index);
						generate(world, solution, options.type(OutputType.table), outdir, cname);
						index++;
						back = 5;
					} while (index < repeat && solution.isIncremental() && (solution = solution.next()).satisfiable());

					if (options.evaluator() && !answers.isEmpty()) {
						evaluator(world, answers);
					}
				}
				n++;
			} catch (Exception e) {
				error("command %s could not be solved: %s", cname, Exceptions.unrollCause(e));
				trace.format("!%s", Exceptions.unrollCause(e));
			}
			trace.format("%n");
		}
	}

	private void showTransformerFile(File source, File outdir, String cname) throws IOException {
		if (outdir == null)
			IO.copy(source, stdout);
		else {
			File out = new File(outdir, cname + "." + ext(source));
			IO.rename(source, out);
		}
		IO.delete(source);
	}

	private String ext(File file) {
		String parts[] = Strings.extension(file.getName());
		if (parts == null)
			return ".unknown";
		else
			return parts[1];
	}

	private String toCName(Command c) {
		StringBuilder sb = new StringBuilder();
		sb.append(c.label);
		return sb.toString();
	}

	private String getStem(File file) {
		String parts[] = Strings.extension(file.getName());
		if (parts == null) {
			return file.getName() + "-output";
		} else
			return parts[0];
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

	private File output(String output, String stem) throws IOException {

		if (output == null)
			output = stem;
		else if (output.equals("--")) {
			return null;
		}

		File dir = IO.getFile(output);
		IO.delete(dir);
		IO.mkdirs(dir);
		if (!dir.isDirectory()) {
			error("Cannot create parent directory for %s", dir);
			return null;
		}
		return dir;

	}

	private void generate(CompModule world, A4Solution solution, OutputType type, File outdir, String cname)
			throws Exception {
		switch (type) {
		default:
		case none:
			return;

		case text:
			try (PrintWriter pw = getPrintWriter(outdir, cname, ".txt")) {
				pw.println(solution.toString());
			}
			return;

		case table:
			try (PrintWriter pw = getPrintWriter(outdir, cname, ".md")) {
				int n = solution.getLoopState();
				if (solution.getTraceLength() < 2)
					n = -1;

				for (int i = 0; i < solution.getTraceLength(); i++) {
					Table t = solution.toTable(i);
					if (n == i) {
						pw.println("--loopstate->");
					}
					pw.println(t);
					List<ExprVar> skolems = solution.getAllSkolems();
					if (!skolems.isEmpty()) {
						Table skolemsTable = new Table(skolems.size() + 1, 2, 1);
						skolemsTable.set(0, 0, "skolem");
						skolemsTable.set(0, 1, "value");
						for (int j = 0; i < skolems.size(); j++) {
							ExprVar var = skolems.get(j);
							Object eval = solution.eval(var, i);
							if (eval instanceof SimTupleset) {
								Table tt = TableView.toTable((SimTupleset) eval);
								skolemsTable.set(j + 1, 1, tt);
							} else
								skolemsTable.set(j + 1, 1, eval);
							skolemsTable.set(j + 1, 0, var.label);
						}
						pw.println(skolemsTable);
					}
				}
			}
			break;

		case json:
			JSONCodec codec = new JSONCodec();
			codec.enc().writeDefaults().indent("  ").to(getPrintWriter(outdir, cname, ".json")).put(solution.toDTO());
			break;

		case xml:
			try (PrintWriter pw = getPrintWriter(outdir, cname, ".xml")) {
				A4SolutionWriter.writeInstance(null, solution, pw, Collections.emptyList(), Collections.emptyMap());
			}
			break;
		}
	}

	private PrintWriter getPrintWriter(File outdir, String cname, String extension) throws IOException {
		if (outdir == null)
			return new PrintWriter(stdout);

		File file = new File(outdir, cname + extension);
		return new PrintWriter(IO.writer(file));
	}

	@Override
	public String toString() {
		return "CLI";
	}
}
