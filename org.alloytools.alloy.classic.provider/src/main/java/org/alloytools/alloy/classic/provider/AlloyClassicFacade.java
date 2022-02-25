package org.alloytools.alloy.classic.provider;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.ServiceLoader;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.allotools.services.util.Services;
import org.alloytools.alloy.core.api.Alloy;
import org.alloytools.alloy.core.api.Compiler;
import org.alloytools.alloy.core.api.CompilerMessage;
import org.alloytools.alloy.core.api.Module;
import org.alloytools.alloy.core.api.Position;
import org.alloytools.alloy.core.api.Solver;
import org.alloytools.alloy.core.api.SourceResolver;
import org.alloytools.alloy.core.api.Visualizer;
import org.alloytools.alloy.core.spi.AlloySolverFactory;
import org.alloytools.alloy.core.spi.AlloyVisualizerFactory;
import org.alloytools.metainf.util.ManifestAccess;

import aQute.lib.io.IO;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ErrorAPI;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.ErrorType;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
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
                List<CompilerMessage> errors = new ArrayList<>();
                List<CompilerMessage> warnings = new ArrayList<>();
                try {
                    CompModule module = CompUtil.parseEverything_fromString(reporter, source);
                    return new AlloyModuleClassic(module, path, source, compiler(), options);
                } catch (ErrorAPI eapi) {
                    errors.add(new ClassicCompilerMessage(path, source, eapi.msg, eapi.pos));
                } catch (ErrorFatal eapi) {
                    errors.add(new ClassicCompilerMessage(path, source, eapi.msg, eapi.pos));
                } catch (ErrorSyntax eapi) {
                    errors.add(new ClassicCompilerMessage(path, source, eapi.msg, eapi.pos));
                } catch (ErrorType eapi) {
                    errors.add(new ClassicCompilerMessage(path, source, eapi.msg, eapi.pos));
                } catch (ErrorWarning eapi) {
                    warnings.add(new ClassicCompilerMessage(path, source, eapi.msg, eapi.pos));
                } catch (Exception e) {
                    warnings.add(new ClassicCompilerMessage(path, source, e.getMessage(), Position.unknown()));
                }
                AlloyModuleClassic m = new AlloyModuleClassic(null, path, source, compiler(), options);
                m.errors.addAll(errors);
                m.warnings.addAll(warnings);
                return m;
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

    @Override
    public String getVersion() {
        Optional<String> header = ManifestAccess.getHeader("org.alloytools.alloy.dist", "Bundle-Version");
        return header.orElse("0.0.0");
    }

    @Override
    public String toString() {
        return "AlloyClassicFacade [solvers=" + solvers + "]";
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
