package org.alloytools.alloy.classic.provider;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import org.allotools.services.util.Services;
import org.alloytools.alloy.core.api.Alloy;
import org.alloytools.alloy.core.api.Compiler;
import org.alloytools.alloy.core.api.CompilerMessage;
import org.alloytools.alloy.core.api.Module;
import org.alloytools.alloy.core.api.Solver;
import org.alloytools.alloy.core.api.SourceResolver;
import org.alloytools.alloy.core.api.TCheck;
import org.alloytools.alloy.core.api.TCommand;
import org.alloytools.alloy.core.api.TRun;
import org.alloytools.alloy.core.api.TSig;
import org.alloytools.alloy.core.spi.AlloySolverFactory;
import org.alloytools.metainf.util.ManifestAccess;

import aQute.lib.io.IO;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.parser.CompUtil;

/**
 * 
 */
public class AlloyClassicFacade implements Alloy {
	static String			JNAME_S		= "\\p{javaJavaIdentifierStart}\\p{javaJavaIdentifierPart}*";
	final static Pattern	OPTIONS_P	= Pattern
		.compile("^--option(\\.(?<glob>[\\p{javaJavaIdentifierPart}*?.-]+))?\\s+(?<key>" + JNAME_S
			+ ")\\s*=\\s*(?<value>[^\\s]+)\\s*$", Pattern.MULTILINE);
	final Path				home;

	final List<Solver>	solvers		= new ArrayList<>();
	private File			preferencesDir;

	public AlloyClassicFacade(Path home) {
		this.home = home;
		this.preferencesDir = IO.getFile("~/.alloy/preferences");
	}

	public AlloyClassicFacade() {
		try {
			this.home = Files.createTempDirectory("Alloy-" + getVersion());
			this.home.toFile()
				.deleteOnExit();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
			throw new RuntimeException();
		}
	}

	@Override
	public synchronized List<Solver> getSolvers() {
		if (solvers.isEmpty()) {
			for (AlloySolverFactory factory : Services.getServices(AlloySolverFactory.class)) {
				solvers.addAll(factory.getAvailableSolvers(this));
			}
		}
		return solvers;
	}

	@Override
	public Optional<Solver> getSolver(String id) {
		return getSolvers().stream()
			.filter(s -> s.getId()
				.equals(id))
			.findAny();
	}

	@Override
	public Compiler compiler(SourceResolver resolver) {
		return new Compiler() {

			@Override
			public Module compile(File file) {
				try {
					return compileSource(new String(Files.readAllBytes(file.toPath()), "UTF-8"));
				} catch (IOException e) {
					e.printStackTrace();
					throw new RuntimeException(e);
				}
			}

			@Override
			public Module compileSource(String source) {
				return compileSource(null, source);
			}

			Module compileSource(String path, String source) {
				List<Option> options = getOptions(source);

				A4Reporter reporter = new A4Reporter();

				try {
					CompModule module = CompUtil.parseEverything_fromString(reporter, source);
					return new AlloyModuleClassic() {

						@Override
						public Set<TSig> getSigs() {
							ConstList<Sig> sigs = module.getAllReachableSigs();
							return new HashSet<>(sigs);
						}

						@Override
						public Optional<TSig> getSig(String name) {
							return getSigs().stream()
								.filter(s -> s.getName()
									.equals(name))
								.findAny();
						}

						@Override
						public List<TRun> getRuns() {
							Module THIS = this;
							return module.getAllCommands()
								.stream()
								.filter(c -> !c.isCheck())
								.map(r -> (TRun) new AbstractCommand(this, r))
								.collect(Collectors.toList());
						}

						@Override
						public List<TCheck> getChecks() {
							Module THIS = this;
							return module.getAllCommands()
								.stream()
								.filter(c -> c.isCheck())
								.map(r -> (TCheck) new AbstractCommand(this, r))
								.collect(Collectors.toList());
						}

						@Override
						public CompModule getOriginalModule() {
							return module;
						}

						@Override
						public Optional<String> getPath() {
							return Optional.ofNullable(path);
						}

						@Override
						public List<CompilerMessage> getWarnings() {
							return Collections.emptyList();
						}

						@Override
						public List<CompilerMessage> getErrors() {
							return Collections.emptyList();
						}

						@Override
						public boolean isValid() {
							return getErrors().isEmpty();
						}

						@Override
						public String toString() {
							return module.toString();
						}

						@Override
						public Map<String, String> getSourceOptions(TCommand command) {
							return extractOptions(options, command);
						}

						@Override
						public Compiler getCompiler() {
							return compiler();
						}
					};
				} catch (Exception e) {
					return new AlloyModuleClassic() {

						@Override
						public Optional<String> getPath() {
							return Optional.ofNullable(path);
						}

						@Override
						public Set<TSig> getSigs() {
							return Collections.emptySet();
						}

						@Override
						public Optional<TSig> getSig(String name) {
							return Optional.empty();
						}

						@Override
						public List<TRun> getRuns() {
							return Collections.emptyList();
						}

						@Override
						public List<TCheck> getChecks() {
							return Collections.emptyList();
						}

						@Override
						public List<CompilerMessage> getWarnings() {
							return Collections.emptyList();
						}

						@Override
						public List<CompilerMessage> getErrors() {
							return Collections.singletonList(new CompilerMessage() {

								@Override
								public int line() {
									return 0;
								}

								@Override
								public String getSource() {
									return source;
								}

								@Override
								public String getPath() {
									return null;
								}

								@Override
								public String getMessage() {
									return e.getMessage();
								}

								@Override
								public int column() {
									return 0;
								}

								@Override
								public String toString() {
									return line() + "," + column() + "# " + getMessage();
								}

								@Override
								public int span() {
									// TODO Auto-generated method stub
									return 0;
								}
							});
						}

						@Override
						public boolean isValid() {
							return false;
						}

						@Override
						public CompModule getOriginalModule() {
							return null;
						}

						@Override
						public Map<String, String> getSourceOptions(TCommand command) {
							return Collections.emptyMap();
						}

						@Override
						public Compiler getCompiler() {
							return compiler();
						}
					};
				}
			}

			private List<Option> getOptions(String source) {
				List<Option> options = new ArrayList<>();
				Matcher matcher = OPTIONS_P.matcher(source);
				while (matcher.find()) {
					String glob = matcher.group("glob");
					String key = matcher.group("key");
					String value = matcher.group("value");
					Option option = new Option(glob, key, value);
					options.add(option);
				}
				return options;
			}

			@Override
			public Module compile(String path) {
				return compileSource(resolver.resolve(path));
			}

			@Override
			public String resolve(String path) {
				// TODO Auto-generated method stub
				return null;
			}

		};
	}

	@Override
	public Compiler compiler() {
		return compiler(new SourceResolver() {

			@Override
			public String resolve(String path) {
				File file = new File(path);
				try {
					return new String(Files.readAllBytes(file.toPath()), "UTF-8");
				} catch (IOException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
					throw new RuntimeException(e);
				}
			}
		});
	}

	public static String getVersion() {
		Optional<String> header = ManifestAccess.getHeader("org.alloytools.alloy.classic.provider", "Bundle-Version");
		return header.orElse("0.0.0");
	}

	@Override
	public String toString() {
		return "AlloyClassicFacade [solvers=" + solvers + "]";
	}

	private Map<String, String> extractOptions(List<Option> options, TCommand command) {
		String name = command.getName();
		return options//
			.stream()
			.filter(opt -> {
				Matcher matcher = opt.glob.matcher(name);
				return matcher.matches();
			})//
			.sorted()
			.distinct()
			.collect(Collectors.toMap(option -> option.key, option -> option.value));
	}

	@Override
	public File getPreferencesDir(String id) {
		return new File(preferencesDir, id);
	}
}
