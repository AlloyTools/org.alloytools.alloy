package org.alloytools.alloy.classic.provider;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.ServiceLoader;
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
import org.alloytools.alloy.core.api.TExpression;
import org.alloytools.alloy.core.api.TFunction;
import org.alloytools.alloy.core.api.TRun;
import org.alloytools.alloy.core.api.TSignature;
import org.alloytools.alloy.core.api.Visualizer;
import org.alloytools.alloy.core.spi.AlloySolverFactory;
import org.alloytools.alloy.core.spi.AlloyVisualizerFactory;
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

    static String            JNAME_S     = "\\p{javaJavaIdentifierStart}\\p{javaJavaIdentifierPart}*";
    final static Pattern     OPTIONS_P   = Pattern.compile("^--option(\\.(?<glob>[\\p{javaJavaIdentifierPart}*?.-]+))?\\s+(?<key>" + JNAME_S + ")\\s*=\\s*(?<value>[^\\s]+)\\s*$", Pattern.MULTILINE);
    final Path               home;

    final Map<String,Solver> solvers     = new HashMap<>();
    private File             preferencesDir;
    private List<Visualizer> visualizers = new ArrayList<>();

    public AlloyClassicFacade(Path home) {
        this.home = home;
        this.preferencesDir = IO.getFile("~/.alloy/preferences");
    }

    public AlloyClassicFacade() {
        try {
            this.home = Files.createTempDirectory("Alloy-" + getVersion());
            this.home.toFile().deleteOnExit();
        } catch (IOException e) {
            throw new RuntimeException();
        }
    }

    @Override
    public synchronized Map<String,Solver> getSolvers() {
        if (solvers.isEmpty()) {
            for (AlloySolverFactory factory : Services.getServices(AlloySolverFactory.class)) {
                for (Solver solver : factory.getAvailableSolvers(this)) {
                    Solver duplicate = solvers.put(solver.getId(), solver);
                    assert duplicate == null : "There are multiple solvers with the same name: " + solver.getId() + ": " + solver.getDescription() + " and " + duplicate.getDescription();

                    if (solver.isJavaOnly()) {
                        solvers.put("", solver);
                    }
                }
            }
        }
        return solvers;
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
                        public Map<String,TSignature> getSignatures() {
                            ConstList<Sig> sigs = module.getAllReachableSigs();

                            Map<String,TSignature> all = sigs.stream().collect(Collectors.toMap(sk -> sk.label, sv -> sv));
                            module.getAllSigs().forEach(sig -> {
                                all.put(sig.label.substring("this/".length()), sig);
                            });
                            return all;
                        }

                        @Override
                        public Map<String,TRun> getRuns() {
                            Map<String,TRun> result = new LinkedHashMap<>();
                            module.getAllCommands().stream().filter(c -> !c.isCheck()).map(r -> (TRun) new AbstractCommand(this, r)).forEach(e -> {
                                result.put(e.getName(), e);
                            });
                            assert !result.isEmpty() : "If no commands are present we add a default command";
                            return result;
                        }

                        @Override
                        public Map<String,TCheck> getChecks() {
                            return module.getAllCommands().stream().filter(c -> c.isCheck()).map(r -> (TCheck) new AbstractCommand(this, r)).collect(Collectors.toMap(kc -> kc.getName(), vc -> vc));
                        }

                        @Override
                        public Map<String,TExpression> getFacts() {
                            return module.getAllFacts().toList().stream().collect(Collectors.toMap(pk -> pk.a, pv -> pv.b));
                        }

                        @Override
                        public Map<String,TFunction> getFunctions() {
                            return module.getAllFunc().toList().stream().filter(f -> !f.isPred).collect(Collectors.toMap(pk -> pk.label, pv -> pv));
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
                        public Map<String,String> getSourceOptions(TCommand command) {
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
                        public Map<String,String> getSourceOptions(TCommand command) {
                            return Collections.emptyMap();
                        }

                        @Override
                        public Compiler getCompiler() {
                            return compiler();
                        }

                        @Override
                        public Map<String,TSignature> getSignatures() {
                            return Collections.emptyMap();
                        }

                        @Override
                        public Map<String,TRun> getRuns() {
                            return Collections.emptyMap();
                        }

                        @Override
                        public Map<String,TCheck> getChecks() {
                            return Collections.emptyMap();
                        }

                        @Override
                        public Map<String,TExpression> getFacts() {
                            return Collections.emptyMap();
                        }

                        @Override
                        public Map<String,TFunction> getFunctions() {
                            return Collections.emptyMap();
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

    private Map<String,String> extractOptions(List<Option> options, TCommand command) {
        String name = command.getName();
        return options.stream().filter(opt -> opt.glob.matcher(name).matches()).sorted().distinct().collect(Collectors.toMap(option -> option.key, option -> option.value));
    }

    @Override
    public File getPreferencesDir(String id) {
        return new File(preferencesDir, id);
    }

    @Override
    public List<Visualizer> getVisualizers() {
        if (visualizers.isEmpty()) {
            ServiceLoader.load(AlloyVisualizerFactory.class).forEach(f -> visualizers.addAll(f.getVisualizers()));
        }
        return visualizers;
    }
}
