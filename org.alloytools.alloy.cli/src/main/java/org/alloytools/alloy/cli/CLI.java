package org.alloytools.alloy.cli;

import java.io.File;
import java.io.FilterInputStream;
import java.io.FilterOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.PrintStream;
import java.io.PrintWriter;
import java.time.Instant;
import java.time.ZoneId;
import java.time.format.DateTimeFormatter;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.TreeMap;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import org.alloytools.alloy.dto.CommandDTO;
import org.alloytools.alloy.dto.ExecutionDTO;
import org.alloytools.alloy.dto.SolutionDTO;
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
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Sig;
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
	PrintStream stderr = new PrintStream(new FilterOutputStream(System.err)) {
		public void close() {
			System.err.flush();
		};
	};

	/**
	 * Show the list of solvers
	 */

	/**
	 * Run all 'run' & asserts
	 */

	@Arguments(arg = "path")
	@Description("Execute an Alloy program. This will create a directory with the name of the source "
			+ "file minus the extension. You will find the solutions in this directory. "
			+ "This directory will also contain a receipt.json file that contains the solutions.")
	interface ExecOptions extends Options {
		@Description("The command to run. If no command is specified, the default command will run. The command may specify wildcards to run multiple commands. If the command is an integer, it will run the command with that index.")
		String command();

		@Description("Specify the output type: none, text, table, json, xml")
		OutputType type(OutputType deflt);

		@Description("Specify where the output should go. Default is the a directory with the stem of "
				+ "the name of the source file. If a name is specified, this will become a directory "
				+ "with the different outputs ordered as separate files. A file is generated with "
				+ "the proper extension for the output type (-t/--type) and the name is the name of "
				+ "the command & the solution index. If the directory contains files, specify -f/--force to "
				+ "delete it. If the value is -, all calculated solutions or transformed files "
				+ "are sent to the console.")
		String output();

		@Description("Specify that the output directory is removed and recreated if it contains any files")
		boolean force();

		@Description("If set, the solution will include only those models in which no arithmetic overflows occurred")
		boolean nooverflow();

		@Description("Number of allowed recursion unrolls. Default is -1 (no unrolling)")
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

		@Description("Find multiple solutions, up to this number. Use 0 for as many as can be found. The default is 1, only the first solution.")
		int repeat(int deflt);

	}

	/**
	 * Execute a Alloy program
	 * 
	 * @param options the options to use
	 */
	@Description("Execute an Alloy program. This will create a directory with the name of the source "
			+ "file minus the extension. You will find the solutions in this directory. "
			+ "This directory will also contain a receipt.json file that contains the solutions.")
	public void _exec(ExecOptions options) throws Exception {
		boolean quiet = options.quiet();
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
		if (!file.canRead()) {
			error("Cannot read file %s", file);
			return;
		}
		if (file.isDirectory()) {
			error("%s must be a file, not a directory", file);
			return;
		}


		Map<String, String> cache = new HashMap<>();
		CompModule world = CompUtil.parseEverything_fromFile(rep, cache, filename);

		List<Command> commands = world.getAllCommands();

		Predicate<Command> run = getCommandPredicate(options, commands);

		File outdir = output(options.output(), getStem(file));

		if (outdir != null) {
			if (outdir.isFile()) {
				error("There is a file with the name of the output directory %s", outdir);
				return;
			}
			IO.mkdirs(outdir);
			if (!outdir.isDirectory()) {
				error("Cannot create output directory %s", outdir);
				return;
			}

			boolean filesExist = outdir.listFiles().length > 0;
			if (filesExist) {
				if (options.force()) {
					IO.delete(outdir);
					IO.mkdirs(outdir);
				} else {
					error("The output directory %s contains files. Delete them or use the -f option", outdir);
					return;
				}
			}
		}
		OutputTrace trace = new OutputTrace(quiet || outdir == null ? null : stderr);
		int n = 0;

		int repeat = options.repeat(1);
		if (repeat == 0) {
			repeat = Integer.MAX_VALUE;
		}

		ExecutionDTO receipt = new ExecutionDTO();
		receipt.solver = opt.solver.id();
		receipt.noOverflow = opt.noOverflow;
		receipt.symmetry = opt.symmetry;
		receipt.unrolls = opt.unrolls;
		receipt.coreGranularity = opt.coreGranularity;
		receipt.coreMinimization = opt.coreMinimization;
		receipt.decompose_mode = opt.decompose_mode;
		receipt.inferPartialInstance = opt.inferPartialInstance;
		receipt.skolemDepth = opt.skolemDepth;
		receipt.timestamp = System.currentTimeMillis();
		receipt.repeat = repeat;

		for (Sig sig : world.getAllReachableSigs()) {
			if (sig.isPrivate != null)
				continue;
			receipt.sigs.put(Util.scope(sig.label), Util.toDTO(sig));
		}

		String source = IO.collect(file);

		for (Command c : commands) {

			if (!run.test(c)) {
				trace("ignore command %s", c);
				continue;
			}

			CommandDTO commandReceipt = Util.toDTO(c, source);
			receipt.commands.put(c.label, commandReceipt);

			int index = 0;
			trace.format("%02d. %-5s %-20s ", n, c.check ? "check" : "run", c.label);
			String cname = toCName(c);

			try {
				A4Solution solution = TranslateAlloyToKodkod.execute_commandFromBook(rep, world.getAllReachableSigs(),
						c, opt);

				if (!solution.satisfiable()) {
					if (rep.output != null) {
						trace.format("  %s", cname + "." + ext(rep.output));
						String path = showTransformerFile(rep.output, outdir, cname);
						commandReceipt.transformPath = path;
					} else {
						trace.format("    0       UNSAT", options.repeat(1));
						if (c.expects == 1) {
							trace.format(" expects=%s", c.expects);
							error("'%s' was not satisfied against expectation",c);
						}
					}
				} else {

					int back = 0;
					do {
						solution.setModule(world);
						trace.back(back).format("%5d", index);
						SolutionDTO solutionDTO = solution.toDTO();
						commandReceipt.solution.add(solutionDTO);
						generate(world, solution, options.type(OutputType.table), outdir, cname, index, solutionDTO);
						index++;
						back = 5;
					} while (index < repeat && solution.isIncremental() && (solution = solution.next()).satisfiable());

					trace.back(back).format("%5d/%-5s SAT", index, options.repeat(1), c.expects);
					if (c.expects == 0) {
						trace.format(" expects=%s", c.expects);
						error("'%s' was satisfied against expectation",c);
					}
					trace.format("\n");
					if (options.evaluator()) {
						evaluator(world, solution);
					}
				}
				n++;
				if (outdir != null)
					try {
						File receiptFile = IO.getFile(outdir, "receipt.json");
						new JSONCodec().enc().to(receiptFile).put(receipt).close();
					} catch (Exception e) {
						error("failed to save receipt: %s", e.getMessage());
					}
			} catch (Exception e) {
				exception(e,"command %s could not be solved: %s", cname, Exceptions.unrollCause(e));
				trace.format("!%s", Exceptions.unrollCause(e));
			}
			trace.format("%n");
		}
	}

	private Predicate<Command> getCommandPredicate(ExecOptions options, List<Command> commands) {
		Predicate<Command> run;
		String cmd = options.command();
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
		return run;
	}

	private String showTransformerFile(File source, File outdir, String cname) throws IOException {
		try {
			if (outdir == null) {
				IO.copy(source, stdout);
				return null;
			} else {
				String child = cname + "." + ext(source);
				File out = new File(outdir, child);
				IO.rename(source, out);
				return child;
			}
		} finally {
			IO.delete(source);
		}
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

	private void evaluator(CompModule world, A4Solution sol) throws Exception {
		if (sol.satisfiable()) {
			stdout.println("Evaluator for latest command");
			stdout.flush();
			Evaluator e = new Evaluator(world, sol, stdin, stdout);
			String lastCommand = e.loop();
			if (lastCommand == null || lastCommand.equals("/exit"))
				return;
		}
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

	final static DateTimeFormatter formatter = DateTimeFormatter.ofPattern("'-'yyyyMMdd'T'HH-mm-ss")
			.withZone(ZoneId.systemDefault());

	private File output(String output, String stem) throws IOException {
		if (output == null)
			output = stem;
		else if (output.equals("-")) {
			return null;
		} else if (output.equals("+")) {
			output = stem + "+";
		}

		if (output.endsWith("+")) {
			Instant now = Instant.now();
			String formattedInstant = formatter.format(now);
			output = output.replaceAll("\\+$", formattedInstant);
		}

		File dir = IO.getFile(output);
		IO.mkdirs(dir);
		return dir;

	}

	private File generate(CompModule world, A4Solution solution, OutputType type, File outdir, String cname, int index,
			SolutionDTO dto) throws Exception {
		switch (type) {
		default:
		case none:
			return null;

		case text: {
			File path = getPath(outdir, cname, ".txt", index);
			try (PrintWriter pw = getPrintWriter(path)) {
				pw.println(solution.toString());
			}
			return path;
		}

		case table: {
			File path = getPath(outdir, cname, ".md", index);
			try (PrintWriter pw = getPrintWriter(path)) {
				pw.printf("%-40s %s%n", "Command", cname);
				pw.printf("%-40s %s%n", "Solution index", index);
				int loopstate = -1;
				int tracelength = 1;
				if (solution.isTemporal()) {
					tracelength = solution.getTraceLength();
					loopstate = solution.getLoopState();
					pw.printf("%-40s %s%n", "Trace length", tracelength);
					pw.printf("%-40s %s%n", "Loop state", loopstate);
				}

				for (int trace = 0; trace < tracelength; trace++) {
					pw.println();
					Table t = solution.toTable(trace);
					if (trace == loopstate) {
						Table withLoopstate = new Table(1, 2, 0);
						withLoopstate.set(0, 0, t);
						withLoopstate.set(0, 1, "<-");
						t = withLoopstate;
					}
					if (solution.isTemporal()) {
						pw.printf("%-40s %s%n", "State index", trace);
						if (trace == loopstate) {
							pw.printf("%-40s %s%n", "Loop back", "true");
						}
					}
					pw.println(t);

					List<ExprVar> skolems = solution.getAllSkolems();
					if (!skolems.isEmpty()) {
						Table skolemsTable = new Table(skolems.size() + 1, 2, 1);
						skolemsTable.set(0, 0, "skolem");
						skolemsTable.set(0, 1, "value");
						for (int skolem = 0; skolem < skolems.size(); skolem++) {
							ExprVar var = skolems.get(skolem);
							Object eval = solution.eval(var, trace);
							if (eval instanceof SimTupleset) {
								Table tt = TableView.toTable((SimTupleset) eval);
								skolemsTable.set(skolem + 1, 1, tt);
							} else
								skolemsTable.set(skolem + 1, 1, eval);
							skolemsTable.set(skolem + 1, 0, var.label);
						}
						pw.println(skolemsTable);
					}
				}
			}
			return path;
		}

		case json: {
			File path = getPath(outdir, cname, ".json", index);
			JSONCodec codec = new JSONCodec();
			codec.enc().writeDefaults().indent("  ").to(getPrintWriter(path)).put(dto);
			return path;
		}
		case xml:
			File path = getPath(outdir, cname, ".xml", index);
			try (PrintWriter pw = getPrintWriter(path)) {
				A4SolutionWriter.writeInstance(null, solution, pw, Collections.emptyList(), Collections.emptyMap());
			}
			return path;
		}
	}

	private File getPath(File outdir, String cname, String extension, int index) {
		if (outdir == null)
			return null;
		return new File(outdir, cname + "-solution-" + index + extension);
	}

	private PrintWriter getPrintWriter(File file) throws IOException {
		if (file == null)
			return new PrintWriter(stdout);

		return new PrintWriter(IO.writer(file));
	}

	@Override
	public String toString() {
		return "CLI";
	}
}
