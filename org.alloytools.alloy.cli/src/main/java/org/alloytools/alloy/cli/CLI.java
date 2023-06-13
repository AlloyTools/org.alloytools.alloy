package org.alloytools.alloy.cli;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

import org.alloytools.alloy.infrastructure.api.AlloyMain;

import aQute.lib.env.Env;
import aQute.lib.getopt.Arguments;
import aQute.lib.getopt.Description;
import aQute.lib.getopt.Options;
import aQute.lib.io.IO;
import aQute.lib.json.JSONCodec;
import aQute.libg.glob.Glob;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.A4SolutionWriter;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

@AlloyMain(name = { "exec" })
public class CLI extends Env {
	final A4Options		options	= new A4Options();

	public enum OutputType {
		plain, json, xml;
	}

	/**
	 * Show the list of solvers
	 */

	/**
	 * Run all 'run' & asserts
	 */

	@Arguments(arg = "path")
	@Description("Execute an Alloy program")
	interface ExecOptions extends Options {
		@Description("The command to run. If no command is specified, the default command will run. The command may specify wildcards")
		String command();

		@Description("Specify the output type: plain, json, xml")
		OutputType type(OutputType deflt);

		@Description("Specify where the output should go. Default is the console")
		String output();
		
		@Description("If set, forbids overflow from occurring")
		boolean nooverflow();
		
		@Description("Number of allowed recursion unrolls. Default is -1, which indicates no unrolls")
		int unrolls(int n);
		@Description("Depth for skolem analysis, default is 0")
		int depth(int n);
		
		@Description("Symmetry breaking")
		int symmetry(int n);
	}

	/**
	 * 
	 * @param options
	 * @throws Exception
	 */
	public void _exec(ExecOptions options) throws Exception {
		SimpleReporter rep = new SimpleReporter(this);
		A4Options opt = this.options.dup();
		opt.noOverflow = options.nooverflow();
		opt.unrolls = options.unrolls(-1);
		opt.skolemDepth = options.depth(opt.skolemDepth);
		opt.symmetry = options.depth(opt.symmetry);
		
		String filename = options._arguments().remove(0);

		Map<String, String> cache = new HashMap<>();
		CompModule world = CompUtil.parseEverything_fromFile(rep, cache, filename);

		Glob glob;
		if (options.command() != null) {
			glob = new Glob(options.command());
		} else
			glob = Glob.ALL;

		for (Command c : world.getAllCommands()) {

			if (!glob.matches(c.label)) {
				continue;
			}

			A4Solution s = TranslateAlloyToKodkod.execute_commandFromBook(rep, world.getAllReachableSigs(), c,
					opt);

			String output = options.output();
			OutputType type = options.type(OutputType.plain);
			String result = generate(options, world, s, type);
			output(options, output, result);
		}

	}

	private void output(ExecOptions options, String output, String result) throws IOException {
		if (output != null) {
			File file = getFile(options.output());
			if (!file.getParentFile().isDirectory()) {
				error("The parent directory of the output file %s does not exist", file);
			} else if (!file.canWrite()) {
				error("Cannot write %s", file);
			} else {
				IO.store(result, file);
			}
		} else {
			System.out.println(result);
		}
	}

	private String generate(ExecOptions options, CompModule world, A4Solution s, OutputType type) throws Exception {
		switch (type) {
		default:
			error("Invalid `type` option %s, using `plain`", options.type(OutputType.plain));
			// fall through
		case plain:
			return s.toTable().toString();

		case json:
			s.setModule(world);
			JSONCodec codec = new JSONCodec();
			return codec.enc().writeDefaults().indent("  ").put(s.toDTO()).toString();

		case xml:
			StringWriter sw = new StringWriter();
			try (PrintWriter pw = new PrintWriter(sw)) {
				A4SolutionWriter.writeInstance(null, s, pw, Collections.emptyList(), Collections.emptyMap());
				return sw.toString();
			}
		}
	}
}
