package org.alloytools.alloy.cli;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.Formatter;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;

import org.allotools.services.util.Services;
import org.alloytools.alloy.core.api.Alloy;
import org.alloytools.alloy.core.api.IRelation;
import org.alloytools.alloy.core.api.Instance;
import org.alloytools.alloy.core.api.Module;
import org.alloytools.alloy.core.api.Solution;
import org.alloytools.alloy.core.api.Solver;
import org.alloytools.alloy.core.api.TCommand;
import org.alloytools.alloy.core.api.TFunction;
import org.alloytools.util.table.Table;
import org.alloytools.util.table.TableView;

import aQute.lib.getopt.Arguments;
import aQute.lib.getopt.CommandLine;
import aQute.lib.getopt.Description;
import aQute.lib.getopt.Options;
import aQute.lib.io.IO;
import aQute.lib.justif.Justif;
import aQute.lib.strings.Strings;
import aQute.libg.qtokens.QuotedTokenizer;
import jline.console.ConsoleReader;

public class Shell implements AutoCloseable {
	final ShellOptions	options;
	final CLI			env;
	final Alloy			alloy;

	File				file;
	Module				module;
	Solution			solution;
	Iterator<Instance>	iterator;
	Instance			instance;

	boolean				boxes	= true;

	static class IgnoreException extends RuntimeException {
		private static final long serialVersionUID = 1L;
	}

	@Description("Start an interactive shell")
	@Arguments(arg = "source.als")
	interface ShellOptions extends Options {
		@Description("Print out tuples as text instead of boxes")
		boolean text();
	}

	public Shell(CLI env, File file, ShellOptions options) {
		this.env = env;
		this.file = file;
		this.options = options;
		this.boxes = !options.text();
		this.alloy = Services.getService(Alloy.class);
		compile(file);
	}

	@Arguments(arg = "...")
	interface RunOptions extends Options {

	}

	public void _run(RunOptions options) throws IOException {
		run(options, true);
		print();
	}

	public void _check(RunOptions options) throws IOException {
		run(options, false);
	}

	private void run(RunOptions options, boolean run) throws IOException {
		if (options._arguments().isEmpty()) {
			doCommand("Default", run, options);
		} else {
			String arg = options._arguments().get(0);
			if (arg.equals("{")) {
				String join = "run __ " + Strings.join(" ", options._arguments());
				String collect = IO.collect(file);
				String content = collect + "\n\n" + join + "\n";
				module = alloy.compiler().compileSource(content);
				doCommand("__", run,options);
			} else {
				for (String a : options._arguments()) {
					doCommand(a, run, options);
				}
			}
		}
	}

	private void doCommand(String name, boolean run, RunOptions options2) throws IOException {
		TCommand cmd = run ? module.getRuns().get(name) : module.getChecks().get(name);
		if (cmd == null) {
			Optional<TFunction> fun = module.getFunctions().stream().filter(f -> f.isPredicate() && f.getName().equals(name)).findAny();
			if (fun.isPresent()) {
				String join = "run "+ name  + "\n";
				String collect = IO.collect(file);
				String content = collect + "\n\n" + join + "\n";
				module = alloy.compiler().compileSource(content);
				doCommand(name, run, options2);
				return;
			}
			env.error("%s %s not found, available command %s", run ? "run" : "check", name, module.getRuns().keySet());
			return;
		}
		Solver solver = alloy.getSolvers().get("");
		this.solution = solver.solve(cmd, null);
		this.iterator = solution.iterator();
		if (!this.iterator.hasNext()) {
			env.error("No solution for %s", cmd);
			return;
		}
		next(1);

	}

	private void next(int n) {
		while (n > 0) {
			if (!this.iterator.hasNext()) {
				env.error("No more solutions");
				return;
			}
			this.instance = this.iterator.next();
			n--;
		}
	}

	private void print() {
		Map<String, Table> table = TableView.toTable(solution, instance);
		table.remove("Int");
		table.remove("seq/Int");
		table.remove("univ");
		table.forEach((k, v) -> {
			System.out.println(k);
			System.out.print(v);
		});
	}

	private void print(IRelation relation) {
		System.out.println(TableView.toTable(relation));
	}

	@Description("Solve for the next solution")
	@Arguments(arg = {})
	interface NextOptions extends Options {
	}

	@Description("Solve for the next solution")
	public void _next(NextOptions options) throws IOException {
		if (check()) {
			next(1);
			print();
		}
	}

	@Description("Try to find a solution where the given condition is true")
	@Arguments(arg = { "..." })
	interface FindOptions extends Options {
		boolean print();
	}

	public void _find(FindOptions options) throws IOException {
		if (check()) {
			String line = Strings.join(" ", options._arguments());
			while (iterator.hasNext()) {
				IRelation eval = instance.eval(line);
				if (eval.isTrue()) {
					print();
					return;
				}
			}
			env.error("No more solutions");
		}
	}

	@Arguments(arg = {})
	interface PrintOptions extends Options {
		boolean text();
	}

	public void _print(PrintOptions options) throws IOException {
		if (check()) {
			if (options.text()) {
				System.out.println(instance);
			} else {
				print();
			}
		}
	}

	@Arguments(arg = { "[file]" })
	interface CompileOptions extends Options {
	}

	public void _compile(CompileOptions options) throws IOException {

		File file = options._arguments().isEmpty() ? this.file : env.getFile(options._arguments().get(0));
		if (file.isFile()) {
			this.file = file;
			compile(file);
		} else {
			env.error("No such file %s", file);
		}
	}

	private boolean check() throws IOException {
		if (module.isValid()) {
			if (solution == null) {
				doCommand("Default", true, null);
				if (!iterator.hasNext()) {
					env.error("no solutions");
					return false;
				}
				instance = iterator.next();
				return true;
			} else if (!iterator.hasNext()) {
				env.error("no more solutions");
				return false;
			}
			return true;
		} else {
			module.getErrors().forEach(e -> env.error("%s", e));
			module.getWarnings().forEach(e -> env.warning("%s", e));
		}
		return false;
	}

	private void compile(File file) {
		this.module = alloy.compiler().compile(file);
		this.solution = null;
		this.instance = null;
		this.iterator = null;

		if (!module.isValid()) {
			module.getErrors().forEach(e -> env.error("%s", e));
			module.getWarnings().forEach(e -> env.warning("%s", e));
		}

	}

	/**
	 * Show the value of a macro
	 *
	 * @throws Exception
	 */
	@Description("Show macro value")
	public void loop() throws Exception {

		try (ConsoleReader reader = new ConsoleReader(); PrintWriter out = new PrintWriter(reader.getOutput())) {
			reader.setPrompt("> ");

			for (String line; (line = reader.readLine()) != null;) {
				out.flush();

				line = line.trim();
				if (line.isEmpty() || line.startsWith("--") || line.startsWith("//"))
					continue;

				QuotedTokenizer qt = new QuotedTokenizer(line, " ", false, false);
				List<String> parts = qt.getTokenSet();
				String cmd = parts.remove(0);
				if (cmd == "/exit")
					return;

				try {
					if (cmd.startsWith("/")) {
						CommandLine cl = new CommandLine(env);
						String help = cl.execute(this, cmd.substring(1), parts);
						if (help != null) {
							System.out.println(help);
						}
					} else {
						if (check()) {
							IRelation eval = instance.eval(line);
							print(eval);
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

	@Override
	public void close() throws Exception {
	}

}
