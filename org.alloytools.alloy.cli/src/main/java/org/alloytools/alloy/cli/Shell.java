package org.alloytools.alloy.cli;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Formatter;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import aQute.lib.getopt.Arguments;
import aQute.lib.getopt.CommandLine;
import aQute.lib.getopt.Description;
import aQute.lib.getopt.Options;
import aQute.lib.io.IO;
import aQute.lib.strings.Strings;
import aQute.libg.qtokens.QuotedTokenizer;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;
import jline.console.ConsoleReader;

public class Shell implements AutoCloseable {
	final ShellOptions			options;
	final CLI					env;
	final Map<String, String>	cache		= new HashMap<>();

	File						file;
	Module						world;
	final List<A4Solution>		solutions	= new ArrayList<>();

	static class IgnoreException extends RuntimeException {
		private static final long serialVersionUID = 1L;
	}

	interface ShellOptions extends Options {

	}

	public Shell(CLI env, File file, ShellOptions options) {
		this.env = env;
		this.file = file;
		this.options = options;
	}

	@Arguments(arg = "[name]")
	interface ExecOptions extends Options {

	}

	public void _exec(ExecOptions options) throws IOException {
		List<String> args = options._arguments();
		if (args.isEmpty()) {
			doCommand(null);
			return;
		}

		String name = args.remove(0);
		Command c = getCommand(name);
		if (c == null) {

			env.error("No such command %s, commands available are %s", name, world.getAllCommands());
			return;
		}
	}

	private Command getCommand(String name) {
		return world.getAllCommands().stream().filter(cc -> cc.label.equals(name)).findAny().orElse(null);
	}

	@Arguments(arg = "...")
	interface RunOptions extends Options {

	}

	public void _run(RunOptions options) throws IOException {
		String join = "run __foo " + Strings.join(" ", options._arguments());
		String collect = IO.collect(file);
		String content = collect + "\n\n" + join + "\n";
		cache.put(file.getAbsolutePath(), content);
		compile();
		Command command = getCommand("__foo");
		if ( command != null) {
			doCommand(command);
		}
	}
	
	public void _cache(Options options) {
		System.out.println(cache);
	}

	@Arguments(arg = {})
	interface NextOptions extends Options {
		boolean print();
	}

	public void _next(NextOptions options) throws IOException {
		A4Solution s = getSolution().next();
		if (options.print())
			System.out.println(s);
		add(s);
	}

	@Arguments(arg = { "..." })
	interface FindOptions extends Options {
		boolean print();
	}

	public void _find(FindOptions options) throws IOException {
		String line = Strings.join(" ", options._arguments());

		Expr match = getWorld().parseOneExpressionFromString(line);
		A4Solution s = getSolution();
		while (s.satisfiable()) {
			Object eval = s.eval(match);
			if (isTrue(eval)) {
				add(s);
				return;
			}
			s = s.next();
		}
		System.out.println("not found");
	}

	private boolean isTrue(Object eval) {
		if (eval == null)
			return false;

		try {
			return (Boolean) eval;
		} catch (Exception e) {
			System.out.println(eval.getClass() + "'" + eval + "'");
		}
		return false;
	}

	public void _prev(NextOptions options) throws IOException {
		pop();
		if (options.print()) {
			System.out.println(getSolution());
		}
	}

	@Arguments(arg = {})
	interface PrintOptions extends Options {
		boolean text();
	}

	public void _print(PrintOptions options) throws IOException {
		A4Solution s = getSolution();
		if (options.text()) {
			System.out.println(s);
		} else {
			String format = s.format(0);
			System.out.println(format);
		}
	}

	@Arguments(arg = { "file" })
	interface CompileOptions extends Options {
	}

	public void _compile(CompileOptions options) throws IOException {
		cache.clear();
		String path = options._arguments().get(0);
		File file = env.getFile(path);
		if (file.isFile()) {
			this.file = file;
			compile();
		} else {
			env.error("No such file %s", path);
		}

	}

	@Arguments(arg = {})
	interface SigOptions extends Options {
		boolean xtended();
	}

	public void _sigs(SigOptions options) throws IOException {
		Module world = getWorld();
		for (Sig sig : world.getAllSigs()) {
			if (options.xtended()) {
				try (Formatter f = new Formatter()) {
					if (sig.ambiguous) {
						f.format("? ");
					}
					if (sig.isAbstract != null) {
						f.format("abstract ");
					}
					if (sig.isEnum != null) {
						f.format("enum ");
					}
					if (sig.isLone != null) {
						f.format("lone ");
					}
					if (sig.isMeta != null) {
						f.format("meta ");
					}
					if (sig.isOne != null) {
						f.format("one ");
					}
					if (sig.isPrivate != null) {
						f.format("private ");
					}
					if (sig.isSome != null) {
						f.format("some ");
					}
					if (sig.isVariable != null) {
						f.format("var ");
					}
					f.format("%s", sig.label);
					System.out.println(f);
				}
			} else
				System.out.printf("%s\n", sig);
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

				if (cmd.startsWith("/")) {
					CommandLine cl = new CommandLine(env);
					String help = cl.execute(this, cmd.substring(1), parts);
					if (help != null) {
						System.out.println(help);
					}
				} else
					try {
						Expr e = getWorld().parseOneExpressionFromString(line);
						Object o = getSolution().eval(e);
						System.out.println(o);
					} catch (Exception e) {
						if (e.getClass() != Exception.class)
							env.exception(e, "%s %s", e.getMessage(), line);
					}
				env.report(System.out);
				env.getErrors().clear();
				env.getWarnings().clear();
			}
		}

	}

	private Module getWorld() throws IOException {
		if (world == null) {
			if (file == null) {
				env.error("No file name, use /compile first");
				throw new IgnoreException();
			}
			SimpleReporter rep = new SimpleReporter(env);
			this.world = CompUtil.parseEverything_fromFile(rep, cache, file.getAbsolutePath());
		}
		return this.world;
	}

	private void add(A4Solution solution) throws IOException {
		if (solution != null && (solutions.isEmpty() || solution != getSolution())) {
			solutions.add(0, solution);
		}
	}

	private void pop() throws IOException {
		if (solutions.isEmpty())
			return;
		solutions.remove(0);
	}

	private A4Solution getSolution() throws IOException {
		if (solutions.isEmpty()) {
			doCommand(null);
		}
		return solutions.get(0);
	}

	private void compile() throws IOException {
		SimpleReporter s = new SimpleReporter(env);
		this.world = CompUtil.parseEverything_fromFile(s, cache, file.getAbsolutePath());
		solutions.clear();
	}

	private void doCommand(Command c) throws IOException {
		if (c == null) {
			c = getWorld().getAllCommands().get(0);
		}
		SimpleReporter rep = new SimpleReporter(env);
		A4Solution s = TranslateAlloyToKodkod.execute_commandFromBook(rep, world.getAllReachableSigs(), c,
				env.options);
		add(s);
	}

	@Override
	public void close() throws Exception {
	}

}
