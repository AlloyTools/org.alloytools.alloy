package org.alloytools.alloy.cli;

import java.io.InputStream;
import java.io.OutputStream;
import java.io.PrintWriter;
import java.util.List;
import java.util.stream.Collectors;

import aQute.lib.env.Env;
import aQute.lib.getopt.Arguments;
import aQute.lib.getopt.CommandLine;
import aQute.lib.getopt.Description;
import aQute.lib.getopt.Options;
import aQute.libg.qtokens.QuotedTokenizer;
import edu.mit.csail.sdg.alloy4.TableView;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.translator.A4Solution;
import jline.console.ConsoleReader;
import jline.console.completer.StringsCompleter;

/**
 * An evaluator based on a current {@link A4Solution}
 */
public class Evaluator extends Env {
	final CompModule	world;

	A4Solution			current;
	int					state		= 0;
	String				returnValue	= null;

	final InputStream	in;
	final OutputStream	out;

	public Evaluator(CompModule world, A4Solution solution, InputStream in, OutputStream out) {
		this.world = world;
		this.current = solution;
		this.in = in;
		this.out = out;
	}

	String loop() throws Exception {

		try (ConsoleReader reader = new ConsoleReader(in, out);
				PrintWriter out = new PrintWriter(reader.getOutput())) {
			reader.setPrompt("> ");
			CommandLine cl = new CommandLine(this);
			doCompletions(reader, cl);

			for (String line; (line = reader.readLine()) != null;) {
				try {
					out.flush();

					line = line.trim();
					if (line.isEmpty() || line.startsWith("--") || line.startsWith("//"))
						continue;

					QuotedTokenizer qt = new QuotedTokenizer(line, " ", false, false);
					List<String> parts = qt.getTokenSet();
					String cmd = parts.remove(0);

					if (cmd.startsWith("/")) {
						String help = cl.execute(this, cmd.substring(1), parts);
						if (help != null) {
							out.println(help);
						}

						if (returnValue != null)
							return returnValue;

					} else
						try {
							world.clearGlobals();
			                for (ExprVar a : current.getAllAtoms()) {
			                    world.addGlobal(a.label, a);
			                }
			                for (ExprVar a : current.getAllSkolems()) {
			                    world.addGlobal(a.label, a);
			                }

							Expr e = world.parseOneExpressionFromString(line);
							Object o = current.eval(e, state);
							if (o != null) {
								String s = o.toString();
								if (TableView.isTable(s)) {
									o = TableView.toTable(s, false);
								}
								out.println(o);
							}
						} catch (Exception e) {
							if (e.getClass() != Exception.class)
								exception(e, "%s %s", e.getMessage(), line);
						}
				} catch (Exception e) {
					exception(e, "unknown error, last line %s", line);
				}
				report(out);
				getErrors().clear();
				getWarnings().clear();
			}
		}
		return null;
	}

	@Description("Show basic information about the current solution")
	interface InfoOptions extends Options {

	}

	@Arguments(arg = {})
	@Description("Show basic information about the current solution")
	public void _info(InfoOptions options) {
		System.out.println(state + "/" + (current.getTraceLength() - 1));
	}

	@Arguments(arg = {})
	@Description("Set the next state if possible")
	interface NextOptions extends InfoOptions {

	}

	@Description("Set the state to the next state if possible")
	public void _next(NextOptions options) {
		if (state + 1 < current.getTraceLength()) {
			state++;
		}
		_info(options);
	}

	@Arguments(arg = "new-state")
	@Description("Adjust the state to a new state. Requires one argument")
	interface StateOptions extends InfoOptions {

	}

	@Description("Adjust the state to a new state. Requires one argument")
	public void _state(StateOptions options) {
		String arg = options._arguments().remove(0);
		if (!arg.matches("[\\d]+")) {
			error("not a valid state %s", arg);
			return;
		}

		int st = Integer.parseInt(arg);
		if (st >= current.getTraceLength()) {
			error("state must be less than %s but is %s", current.getTraceLength(), st);
			return;
		}
		this.state = st;
		_info(options);
	}

	@Arguments(arg = {})
	@Description("Set the previous state if possible")
	interface PrevOptions extends InfoOptions {

	}

	@Description("Set the previous state if possible")
	public void _prev(PrevOptions options) {
		if (state > 0) {
			state--;
		}
		_info(options);
	}

	@Arguments(arg = {})
	@Description("exit the shell completely, no continuation even if there is a next solution")
	interface ExitOptions extends Options {

	}

	@Description("exit the shell completely, no continuation even if there is a next solution")
	public void _exit(ExitOptions opts) {
		returnValue = "/exit";
	}

	@Arguments(arg = {})
	@Description("continue the next solution, if there is one")
	interface ContinueOptions extends Options {

	}

	@Description("exit the shell completely, not continuation if there is a next solution")
	public void _continue(ContinueOptions opts) {
		returnValue = "/continue";
	}

	private void doCompletions(ConsoleReader reader, CommandLine cl) {
		List<String> completions = cl.getCommands(this).keySet().stream().map(s -> "/" + s)
				.collect(Collectors.toList());
		completions.add("/exit");
		completions.add("/continue");

		world.getAllFunc().forEach(f -> completions.add(f.label));
		world.getAllReachableSigs().forEach(s -> {
			String label = s.label;
			int n = label.lastIndexOf('/');
			if (n >= 0) {
				label = label.substring(n + 1);
			}
			completions.add(label);
			s.getFields().forEach(field -> {
				completions.add(field.label);
			});
		});

		reader.addCompleter(new StringsCompleter(completions));
	}

}
