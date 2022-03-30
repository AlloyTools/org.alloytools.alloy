package org.alloytools.alloy.cli;

import java.io.File;
import java.io.IOException;
import java.lang.reflect.Field;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.alloytools.alloy.core.api.Alloy;
import org.alloytools.alloy.core.api.AlloyOptions;
import org.alloytools.alloy.core.api.CompilerMessage;
import org.alloytools.alloy.core.api.TModule;
import org.alloytools.alloy.core.api.Solution;
import org.alloytools.alloy.core.api.Solver;
import org.alloytools.alloy.core.api.SolverOptions;
import org.alloytools.alloy.core.api.TCommand;
import org.alloytools.alloy.core.api.Visualizer.Renderer;
import org.alloytools.alloy.core.api.VisualizerOptions;
import org.alloytools.alloy.infrastructure.api.AlloyCLI;
import org.alloytools.cli.api.CLICommand;

import aQute.lib.converter.Converter;
import aQute.lib.getopt.Arguments;
import aQute.lib.getopt.Options;
import aQute.lib.io.IO;
import aQute.lib.strings.Strings;
import aQute.libg.parameters.Attributes;
import aQute.libg.parameters.ParameterMap;
import aQute.libg.reporter.ReporterAdapter;

@AlloyCLI(subCommand = "solve", isDefault = true)
public class SolveCLI extends ReporterAdapter implements CLICommand {

	final static Pattern	p	= Pattern.compile("\\.(als|md)", Pattern.CASE_INSENSITIVE);

	final Alloy				alloy;

	public SolveCLI(Alloy alloy) {
		this.alloy = alloy;
	}

	@Arguments(arg = {
			"file"
	})
	interface SolveOptions extends Options {

		String command();

		String solver();

		String output();

		String renderers(String tableIsDefault);

		int instances(int default1);

		String[] xoptions();
	}

	public void _solve(SolveOptions options) throws IOException {
		List<String> args = options._arguments();

		File f = IO.getFile(args.remove(0));
		if (!f.isFile()) {
			error("no such file %s", f);
			return;
		}
		String content = IO.collect(f);

		File outputdir = f.getParentFile();
		if (options.output() != null) {
			outputdir = IO.getFile(outputdir, options.output());
			if (!outputdir.isDirectory()) {
				outputdir.mkdirs();
				if (!outputdir.isDirectory()) {
					error("the specified output directory %s does not exist", outputdir);
					return;
				}
			}
		}

		String stem = Strings.stripSuffix(f.getName(), p);
		String commandName = options.command();
		if (commandName != null && commandName.startsWith("{")) {
			content = content + "\n\n___: run" + commandName + "\n";
			commandName = "___";
		}

		TModule module = alloy.compiler().compileSource(content);
		if (module.isValid()) {
			for (CompilerMessage m : module.getErrors()) {
				error("%s", m);
			}
			error("not a valid module %s", f);
			return;
		}
		for (CompilerMessage m : module.getWarnings()) {
			warning("%s", m);
		}

		Solver s = alloy.getSolvers().get(options.solver() == null ? "" : options.solver());
		if (s == null) {
			error("not a valid solver %s, available are %s", options.solver(), alloy.getSolvers().keySet());
			return;
		}

		if (!s.isAvailable()) {
			error("solver %s is not available on this platform, available solvers are %s", s,
					alloy.getSolvers().keySet());
			return;
		}

		TCommand command = module.getDefaultCommand();
		if (options.command() != null) {
			command = module.getRuns().get(commandName);
			if (command == null) {
				error("no such command %s, available are %s", module.getRuns().keySet());
				return;
			}
		}

		SolverOptions opts = s.newOptions();
		if (options.xoptions() != null) {

			for (String o : options.xoptions()) {
				String[] parts = o.split("\\s*=\\s*");
				if (parts.length == 1) {
					parts = new String[] {
							parts[0], "true"
					};
				}
				try {
					Field field = opts.getClass().getField(parts[0]);
					field.set(opts, Converter.cnv(field.getGenericType(), parts[1]));
				} catch (Exception e) {
					error("unknown option %s=%s", parts[0], parts[1]);
				}
			}
			if (!isOk()) {
				error("For solver %s, possible options are %s", s,
						Stream.of(opts.getClass().getFields()).map(Field::getName).collect(Collectors.toList()));
				return;
			}
		}

		Solution solution = s.solve(command, opts);

		if (!solution.isSatisfied()) {
			error("no solution found");
			return;
		}

		String renderers = options.renderers(null);
		ParameterMap pm = new ParameterMap(renderers);

		for (Map.Entry<String, Attributes> e : pm.entrySet()) {

			Optional<Renderer<Solution, String>> vis = alloy.findRenderer(e.getKey(), Solution.class, String.class);

			if (!vis.isPresent()) {
				error("no such visualizer %s, available visualizers %s", e,
						alloy.getVisualizers());
				return;
			}

			Renderer<Solution, String> renderer = vis.get();
			AlloyOptions<VisualizerOptions> visOpts = renderer.newOptions();
			visOpts.set(e.getValue());

			File out = new File(outputdir, stem + renderer.extension());
			String in = renderer.render(solution, visOpts);
			IO.store(in, out);
		}
	}

}
