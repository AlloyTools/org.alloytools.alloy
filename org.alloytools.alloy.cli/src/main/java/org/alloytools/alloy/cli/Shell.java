package org.alloytools.alloy.cli;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import org.allotools.services.util.Services;
import org.alloytools.alloy.core.api.Alloy;
import org.alloytools.alloy.core.api.IRelation;
import org.alloytools.alloy.core.api.Instance;
import org.alloytools.alloy.core.api.TModule;
import org.alloytools.alloy.core.api.Solution;
import org.alloytools.alloy.core.api.Solver;
import org.alloytools.alloy.core.api.TCommand;
import org.alloytools.alloy.core.api.TFunction;
import org.alloytools.json.util.JSONEncoder;
import org.alloytools.json.util.TextEncoder;
import org.alloytools.util.table.Table;
import org.alloytools.util.table.TableView;

import aQute.lib.getopt.Arguments;
import aQute.lib.getopt.CommandLine;
import aQute.lib.getopt.Description;
import aQute.lib.getopt.Options;
import aQute.lib.io.IO;
import aQute.lib.strings.Strings;
import aQute.libg.qtokens.QuotedTokenizer;
import jline.console.ConsoleReader;

public class Shell implements AutoCloseable {
	final ShellOptions	options;
	final CLI			env;
	final Alloy			alloy;

	File				file;
	TModule				module;
	Solution			solution;
	Iterator<Instance>	iterator;
	Instance			instance;

	boolean				boxes	= true;
	private long		lastCompile;

	static class IgnoreException extends RuntimeException {
		private static final long serialVersionUID = 1L;
	}

	@Description("Start an interactive shell")
	@Arguments(arg = "source.als")
	interface ShellOptions extends Options {
		@Description("Print out tuples as text instead of boxes")
		boolean text();

		boolean quiet();
	}

	public Shell(CLI env, File file, ShellOptions options) {
		this.env = env;
		this.file = file;
		this.options = options;
		this.boxes = !options.text();
		this.alloy = Services.getService(Alloy.class);
		compile(file);
	}

    @Description("Run a predicate from the current source or run a block. E.g. 'run foo for 10' or 'run { some A } for 10'")
	@Arguments(arg = {"pred | body ..."})
	interface RunOptions extends Options {

	}

    @Description("Run a predicate from the current source or run a block. E.g. 'run foo for 10' or 'run { some A } for 10'")
	public void _run(RunOptions options) throws IOException {
		run(options, true);
		print();
	}

	@Arguments(arg = {"{body}|predicate <scope>","..."})
    @Description("Run a check. This is the same as the `alloy` check command. It runs the body with the given scope but the intention is not to find a solution. A found solution is a counter example.")
	interface CheckOptions extends RunOptions {
	    
	}

    @Description("An alloy 'check' command with a run body")
	public void _check(CheckOptions options) throws IOException {
		run(options, false);
	}

	private void run(RunOptions options, boolean run) throws IOException {
		if (options._arguments().isEmpty()) {
			setSolution(doCommand(null, run, options));
		} else {
			String arg = options._arguments().get(0);
			if (arg.startsWith("{")) {
				String join = "run __ " + Strings.join(" ", options._arguments());
				String collect = IO.collect(file);
				String content = collect + "\n\n" + join + "\n";
				module = alloy.compiler().compileSource(content);
				setSolution(doCommand("__", run, options));
			} else {
				for (String a : options._arguments()) {
					setSolution(doCommand(a, run, options));
				}
			}
		}
	}

	private void setSolution(Solution solution) {
		this.solution = solution;
		this.iterator = null;
		this.instance = null;
	}

	private Solution doCommand(String name, boolean run, RunOptions options2) throws IOException {
		TCommand cmd;
		if (run) {
			if (name == null)
				cmd = module.getDefaultCommand();
			else {
				cmd = module.getRuns().get(name);
				if (cmd == null) {
					if (name != null) {
						Optional<TFunction> fun = module.getFunctions().stream()
								.filter(f -> f.isPredicate() && f.getName().equals(name)).findAny();
						if (fun.isPresent()) {
							String join = "run " + name + "\n";
							String collect = IO.collect(file);
							String content = collect + "\n\n" + join + "\n";
							module = alloy.compiler().compileSource(content);
							return doCommand(name, run, options2);
						}
						env.error("%s %s not found, available command %s", run ? "run" : "check", name,
								module.getRuns().keySet());
						return null;
					}
				}
			}
			if (cmd == null) {
				env.error("Cannot find run " + name);
				return null;
			}
		} else {
			if (name == null) {
				env.error("A check has no default, so requires a name");
				return null;
			}
			cmd = module.getChecks().get(name);
			if (cmd == null) {
				env.error("Cannot find check " + name);
				return null;
			}
		}
		Solver solver = alloy.getSolvers().get("");
		return solver.solve(cmd, null);
	}

	private boolean next(int n) {
		while (n > 0) {
			if (!this.iterator.hasNext()) {
				env.error("No more solutions");
				return false;
			}
			this.instance = this.iterator.next();
			n--;
		}
		return true;
	}

	private void print() throws IOException {
		if (check(false)) {
			Map<String, Table> table = TableView.toTable(solution, instance);
			table.remove("Int");
			table.remove("seq/Int");
			table.remove("univ");
			table.forEach((k, v) -> {
				System.out.println(k);
				System.out.print(v);
			});
		}
	}

	private void print(IRelation relation, PrintOptions options) throws Exception {
		if (options != null && options.json()) {
			JSONEncoder.stream(System.out, relation);
		} else if (options != null && options.text()) {
			TextEncoder.stream(System.out, relation);
		} else {
			System.out.println(TableView.toTable(relation));
		}
	}

	private void print(Map<String, IRelation> rs, PrintOptions options) throws Exception {
		if (check(false)) {
			if (options.json()) {
				JSONEncoder.stream(System.out, rs);
			} else {
				List<IRelation> s = new ArrayList<>(rs.values());
				Collections.sort(s);
				int cols = options.horizontal(1);
				if (cols <= 1) {
					s.forEach(r -> System.out.println(TableView.toTable(r)));
				} else {
					int rows = (rs.size() + cols - 1) / cols;
					Table table = new Table(rows, cols, 0);
					int row = 0, col = 0;
					for (IRelation r : s) {
						Table t = TableView.toTable(r);
						table.set(row, col, t.toString());
						col++;
						if (col >= cols) {
							col = 0;
							row++;
						}
					}
					table.setNone();
					System.out.println(table.toString());
				}
			}
		}
	}

	@Description("Solve for the next solution")
	@Arguments(arg = {})
	interface NextOptions extends Options {
	}

	@Description("Resolve for the next solution")
	public void _next(NextOptions options) throws IOException {
		if (check(false)) {
			next(1);
			print();
		}
	}

	@Description("Try to find a instance where the given condition is true. The condition is an alloy expression against the instance")
	@Arguments(arg = { "..." })
	interface FindOptions extends PrintOptions {
	}

    @Description("Try to find an instance where the given condition is true")
	public void _find(FindOptions options) throws IOException {
		if (check(false)) {
			String line = Strings.join(" ", options._arguments());
			while (iterator.hasNext()) {
			    next(1);
				IRelation eval = instance.eval(line);
				if (eval.isTrue()) {
					_print(options);
					return;
				}
			}
			env.error("No more solutions");
		}
	}

    @Description("Print the current instance")
	@Arguments(arg = {})
	interface PrintOptions extends Options {
        @Description("Textual represeentation")
		boolean text();

        @Description("Print n instances horizontal")
		int horizontal(int i);

        @Description("Print a json file")
		boolean json();
	}

    @Description("Print the current instance")
	public void _print(PrintOptions options) throws IOException {
		if (check(false)) {
			if (options.text()) {
				System.out.println(instance);
			} else {
				print();
			}
		}
	}

	@Description("Iterate over all instances and execute an Alloy expression")
	@Arguments(arg = "variable...")
	interface ForEachOptions extends RunOptions, PrintOptions {
	    @Description("Reset the solution")
		boolean again();

        @Description("Run a command before")
		String run();

        @Description("Show duplicate solutions")
		boolean duplicates();

        @Description("Max iterations")
		int max(int deflt);
	}

    @Description("Iterate over all instances and execute an Alloy expression")
	public void _foreach(ForEachOptions options) throws Exception {
		if (options.run() != null) {
			setSolution(doCommand(options.run(), true, options));
		}
		int max = options.max(1000);

		if (check(options.again())) {
			String line = Strings.join(" ", options._arguments());
			Map<String, IRelation> displayed = new HashMap<>();
			int n = 0;
			do {
				if (n++ > max)
					break;

				IRelation eval = instance.eval(line);
				if (!options.duplicates() && displayed.values().contains(eval))
					continue;
				displayed.put(line + "-" + n, eval);
			} while (iterator.hasNext() && next(1));
			print(displayed, options);
		}
	}

    @Description("Open the graphical user interface")
	@Arguments(arg = "file...")
	interface GuiOptions extends RunOptions {
	}

    @Description("Open the graphical user interface")
	public void _edit(GuiOptions options) throws Exception {
		env.background("gui", file.getAbsolutePath());
	}

	@Description("Compile the current or new source file as the base to evalate against")
	@Arguments(arg = { "[file]" })
	interface CompileOptions extends Options {
	}

    @Description("Compile the current or new source file as the base to evalate against")
	public void _compile(CompileOptions options) throws IOException {

		File file = options._arguments().isEmpty() ? this.file : env.getFile(options._arguments().get(0));
		if (file.isFile()) {
			this.file = file;
			compile(file);
		} else {
			env.error("No such file %s", file);
		}
	}

	private boolean check(boolean reset) throws IOException {
		if (file.lastModified() >= lastCompile) {
			compile(file);
		}
		if (module.isValid()) {
			if (solution == null) {
				setSolution(doCommand(null, true, null));
				if (solution == null)
					return false;
			}

			if (iterator == null || reset) {
				iterator = solution.iterator();
				instance = null;
			}

			if (instance == null) {
				if (iterator.hasNext()) {
					instance = iterator.next();
					return true;
				} else {
					env.error("no solutions");
					return false;
				}
			}

			return true;
		} else {
			module.getErrors().forEach(e -> env.error("%s", e));
			module.getWarnings().forEach(e -> env.warning("%s", e));
		}
		return false;
	}

	private boolean reset() throws IOException {
		if (file.lastModified() >= lastCompile) {
			compile(file);
		}
		if (module.isValid()) {
			if (solution == null) {
				env.error("no solutions");
				return true;
			} else {
				iterator = solution.iterator();
				return next(1);
			}
		} else {
			module.getErrors().forEach(e -> env.error("%s", e));
			module.getWarnings().forEach(e -> env.warning("%s", e));
		}
		return false;
	}

    @Description("Reset the solution to the first instance")
	@Arguments(arg = {})
	interface ResetOptions extends Options {
	}

	@Description("Reset the solution to the first instance")
	public void _reset(ResetOptions options) throws IOException {
		reset();
	}

	private void compile(File file) {
		this.module = alloy.compiler().compile(file);
		this.lastCompile = System.currentTimeMillis();
		this.solution = null;
		this.instance = null;
		this.iterator = null;

		if (!module.isValid()) {
			module.getErrors().forEach(e -> env.error("%s", e));
			module.getWarnings().forEach(e -> env.warning("%s", e));
		}

	}

    @Arguments(arg={"alloy..."})
    @Description("Evaluate an Alloy expression using the current instance")
	interface EvalOptions extends PrintOptions {
	}

    @Description("Evaluate an Alloy expression using the current instance")
	public void _eval(EvalOptions options) throws Exception {
		eval(Strings.join(" ", options._arguments()), options);
	}

	/**
	 * Show the value of a macro
	 *
	 * @throws Exception
	 */
	@Description("Show macro value")
	public void loop() throws Exception {

		try (ConsoleReader reader = new ConsoleReader(); PrintWriter out = new PrintWriter(reader.getOutput())) {
			if (!options.quiet())
				out.println("Alloy shell " + alloy.getVersion());
			reader.setPrompt("> ");

			for (String line; (line = reader.readLine()) != null;) {
				out.flush();

				line = line.trim();
				if (line.isEmpty() || line.startsWith("--") || line.startsWith("//"))
					continue;

				QuotedTokenizer qt = new QuotedTokenizer(line, " ", false, false);
				List<String> parts = qt.getTokenSet();
				String cmd = parts.remove(0);
				if (cmd.equals("exit"))
					return;

				try {
					if (cmd.equals(".")) {
						eval(line.substring(1), null);
					} else {
						CommandLine cl = new CommandLine(env);
						String help = cl.execute(this, cmd, parts);
						if (help != null) {
							System.out.println(help);
						}
					}
				} catch (Throwable e) {
					if (e.getClass() != Exception.class)
						env.exception(e, "%s %s", e.getMessage(), line);
				}
				env.report(System.out);
				env.getErrors().clear();
				env.getWarnings().clear();
			}
		}

	}

	private void eval(String line, PrintOptions options) throws Exception {
		if (check(false)) {
			IRelation eval = instance.eval(line);
			print(eval, options);
		}
	}

	@Override
	public void close() throws Exception {
	}

}
