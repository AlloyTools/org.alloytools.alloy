package org.alloytools.alloy.classic.provider;

import java.io.File;
import java.io.IOException;
import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.Type;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.TreeMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.allotools.services.util.Services;
import org.alloytools.alloy.core.api.Alloy;
import org.alloytools.alloy.core.api.AlloyOptions;
import org.alloytools.alloy.core.api.Compiler;
import org.alloytools.alloy.core.api.CompilerMessage;
import org.alloytools.alloy.core.api.TModule;
import org.alloytools.alloy.core.api.Position;
import org.alloytools.alloy.core.api.Solver;
import org.alloytools.alloy.core.api.SourceResolver;
import org.alloytools.alloy.core.api.Visualizer;
import org.alloytools.alloy.core.api.Visualizer.RenderType;
import org.alloytools.alloy.core.api.Visualizer.Renderer;
import org.alloytools.metainf.util.ManifestAccess;

import aQute.bnd.exceptions.Exceptions;
import aQute.lib.converter.Converter;
import aQute.lib.io.IO;
import aQute.libg.glob.Glob;
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

    final Map<String,Solver> solvers     = new TreeMap<>();
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
            for (Solver solver : Services.getServices(Solver.class, this::create)) {
                if (solver.isJavaOnly()) {
                    solvers.put("", solver);
                }
                solvers.put(solver.getId(), solver);
            }
        }
        return solvers;
    }

    @Override
    public Compiler compiler(SourceResolver resolver) {
        return new Compiler() {

            @Override
            public TModule compile(File file) {
                try {
                    return compileSource(new String(Files.readAllBytes(file.toPath()), "UTF-8"));
                } catch (IOException e) {
                    e.printStackTrace();
                    throw new RuntimeException(e);
                }
            }

            @Override
            public TModule compileSource(String source) {
                return compileSource(null, source);
            }

            TModule compileSource(String path, String source) {
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
            public TModule compile(String path) {
                return compileSource(resolver.resolve(path));
            }

            @Override
            public String toString() {
                return "alloy.classic";
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
            Services.getServices(Visualizer.class, this::create).forEach(f -> visualizers.add(f));
        }
        return visualizers;
    }

    public <T> T create(Class<T> type) {
        try {
            Constructor<T> c = type.getConstructor(Alloy.class);
            return c.newInstance(this);
        } catch (Exception e1) {
            try {
                return type.newInstance();
            } catch (InstantiationException | IllegalAccessException e) {
                throw Exceptions.duck(e);
            }
        }
    }

    @Override
    public <A, O> Optional<Renderer<A,O>> findRenderer(String glob, Class<A> argument, Class<O> output) {
        Glob g = new Glob(glob);
        for (Visualizer v : getVisualizers()) {
            if (g.finds(v.getName()) < 0)
                continue;

            for (RenderType rt : v.getRenderTypes()) {

                if (rt.matches(argument, output)) {
                    return Optional.of(rt.instantiate(argument, output));
                }
            }
        }
        return Optional.empty();
    }

    @Override
    public <X> AlloyOptions<X> asOptions(X options) {
        Class< ? > clazz = options.getClass();
        Map<String,Field> fields = Stream.of(clazz.getFields()).filter(field -> {
            int modifiers = field.getModifiers();
            if (Modifier.isStatic(modifiers))
                return false;
            return Modifier.isPublic(modifiers);
        }).collect(Collectors.toMap(f -> f.getName(), f -> f));
        return new AlloyOptions<X>() {

            @Override
            public Iterator<String> iterator() {
                return fields.keySet().iterator();
            }

            @Override
            public Object get(String name) {
                Field field = field(name);
                try {
                    return field.get(options);
                } catch (IllegalArgumentException | IllegalAccessException e) {
                    throw Exceptions.duck(e);
                }
            }

            private Field field(String name) {
                Field field = fields.get(name);
                if (field == null)
                    throw new IllegalArgumentException("no such field " + name);
                return field;
            }

            @SuppressWarnings("unchecked" )
            @Override
            public <T> T get(String name, Class<T> type) {
                Object v = get(name);
                if (v == null)
                    return (T) v;

                return cnv(type, v);
            }

            @Override
            public Object get(String name, Type type) {
                Object v = get(name);
                if (v == null)
                    return v;

                return cnv(type, v);
            }

            @SuppressWarnings("unchecked" )
            @Override
            public <Z> Z get(String name, TypeRef<Z> type) {
                Object v = get(name);
                if (v == null)
                    return (Z) v;

                ParameterizedType pt = (ParameterizedType) type.getClass().getGenericSuperclass();
                return (Z) cnv(pt.getActualTypeArguments()[0], v);
            }

            @SuppressWarnings("unchecked" )
            @Override
            public <T> T set(String name, T value) {
                Field field = field(name);

                try {
                    Object old = field.get(options);
                    Object cnv = cnv(field.getGenericType(), value);
                    field.set(options, cnv);
                    return (T) old;
                } catch (Exception e) {
                    throw Exceptions.duck(e);
                }
            }

            @Override
            public Type type(String name) {
                Field field = field(name);
                return field.getGenericType();
            }


            @Override
            public X get() {
                return options;
            }

            protected <T> T cnv(Class<T> type, Object v) {
                try {
                    return Converter.cnv(type, v);
                } catch (Exception e) {
                    throw Exceptions.duck(e);
                }
            }

            protected Object cnv(Type type, Object v) {
                try {
                    return Converter.cnv(type, v);
                } catch (Exception e) {
                    throw Exceptions.duck(e);
                }
            }

            @Override
            public void set(Map<String, ? > value) {
                value.forEach((k, v) -> {
                    try {
                        set(k, v);
                    } catch (IllegalArgumentException e) {
                    }
                });
            }

        };
    }


}
