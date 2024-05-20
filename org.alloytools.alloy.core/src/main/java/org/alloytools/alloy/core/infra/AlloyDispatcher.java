package org.alloytools.alloy.core.infra;


import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.PrintStream;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.net.URL;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Enumeration;
import java.util.Formatter;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.Properties;
import java.util.function.BiConsumer;
import java.util.jar.Manifest;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import org.alloytools.alloy.context.api.AlloyContext;
import org.alloytools.alloy.infrastructure.api.AlloyMain;
import org.alloytools.util.table.Table;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import aQute.lib.env.Env;
import aQute.lib.getopt.Arguments;
import aQute.lib.getopt.CommandLine;
import aQute.lib.getopt.Description;
import aQute.lib.getopt.Options;
import aQute.lib.io.IO;
import aQute.lib.justif.Justif;
import aQute.lib.strings.Strings;
import aQute.libg.parameters.Attributes;
import aQute.libg.parameters.ParameterMap;
import aQute.service.reporter.Reporter;
import edu.mit.csail.sdg.alloy4.A4Preferences;
import edu.mit.csail.sdg.alloy4.A4Preferences.Pref;
import edu.mit.csail.sdg.translator.A4Solution;
import kodkod.engine.satlab.ExternalSolver;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.satlab.SATSolver;
import kodkod.solvers.api.NativeCode;
import kodkod.solvers.api.NativeCode.Platform;

/**
 * Since the Alloy code is used for many different situations, we do not assume
 * we know how the world looks like. This class uses the AlloyMain annotation to
 * find any class that can be called from the command line that was added to the
 * distribution jar.
 * <p>
 * DO NOT CREATE A LOGGER
 *
 */
@Description("The Alloy dispatcher" )
public class AlloyDispatcher extends Env {

    public static int    exitCode = 0;

    static final Justif  justif   = new Justif(60, 0, 10, 20, 30);

    PrintStream          out      = System.out;
    PrintStream          err      = System.err;
    AlloyContext         context;
    Optional<Manifest>   manifest;
    Logger               log;
    private List<Object> mains;


    enum Levels {
                 off,
                 trace,
                 debug,
                 info,
                 warn,
                 error;
    }



    @Description("The Alloy command line" )
    @Arguments(
               arg = {
                      "[sub-cmd]", "..."
               } )
    interface BaseOptions extends Options {

        @Description("Activate debugging mode" )
        boolean debug();

        @Description("Set the default log level: off, trace, debug, info, warn, error. If not set, defaults to error" )
        Levels defaultLevel(Levels deflt);

        @Description("Set per logger log level. The syntax is <logger-prefix>=<level>, where level is off, trace, debug, info, warn, error" )
        String[] log();
    }

    public static void main(String[] args) {
        AlloyDispatcher dispatcher = new AlloyDispatcher();
        CommandLine cl = new CommandLine(dispatcher);
        try {
            String help = cl.execute(dispatcher, "_alloy", Arrays.asList(args));
            if (help != null) {
                System.err.println(help);
            }
        } catch (Exception e) {
            e.printStackTrace();
        }
        if (exitCode != 0)
            System.exit(exitCode);
    }

    public void __alloy(BaseOptions options) throws Exception {
        if (options.debug())
            System.setProperty("debug", "yes");

        setslf4j(options.debug() ? Levels.debug : options.defaultLevel(Levels.error), options.log());
        log = LoggerFactory.getLogger("alloy");
        if (log.isDebugEnabled())
            log.debug("starting alloy {}", getVersion());

        CommandLine cl = options._command();
        AlloyContext context = getContext(options);

        loadExtensions(new File(context.getHome(), "extensions/sat"));

        mains = getMains(context, cl);
        try {
            List<String> arguments = options._arguments();

            String subcommand = "gui";

            if (!arguments.isEmpty()) {
                subcommand = arguments.remove(0);
                if (subcommand.equals("help"))
                    subcommand = "_help";
            }

            CommandLine l = new CommandLine(this);
            for (Object target : mains) {
                Map<String,Method> commands = l.getCommands(target);
                if (commands.containsKey(subcommand)) {
                    try {
                        log.debug("subcommand {} found in {}", subcommand, target);
                        String info = l.execute(target, subcommand, arguments);
                        if (info != null) {
                            System.out.println(info);
                        }
                    } catch (Exception e) {
                        log.error("excuting sub command {}:{} error {}", target, subcommand, e, e);
                        exception(e, "executing %s:%s", target, subcommand);
                    }
                    if (target instanceof Reporter && target != this) {
                        getInfo((Reporter) target);
                    }
                    if (!getErrors().isEmpty())
                        exitCode = 1;
                    report(System.err);
                    return;
                }
            }
            error("no such command %s, use help to get a full list", subcommand);
            __help(null);
            report(System.err);
            exitCode = 2;
        } finally {
            mains.forEach(o -> {
                if (o instanceof AutoCloseable)
                    IO.close((AutoCloseable) o);
            });
        }
    }


    @Arguments(
               arg = {} )
    @Description("Display the current version" )
    interface VersionOptions extends Options {

        @Description("Show the full major.minor.micro.qualifier version, normal it does not print the qualifier" )
        boolean full();
    }

    @Description("Display the current version" )
    public void _version(VersionOptions options) {
        String version = getVersion();
        if (!options.full()) {
            int n = version.lastIndexOf('.');
            if (n > 0)
                version = version.substring(0, n);
        }
        out.println(version);
    }

    private AlloyContext getContext(BaseOptions options) {
        if (context == null) {
            File home = IO.getFile("~/.alloy");
            context = new AlloyContext() {

                @Override
                public boolean isDebug() {
                    return options.debug();
                }

                @Override
                public File getHome() {
                    return home;
                }
            };
        }
        return context;
    }


    @Description("Show the preferences or modify them" )
    @Arguments(
               arg = {} )
    interface PreferencesOptions extends Options {

        @Description("Show the preferences in a comma separated format as used by the alloy `-p` preferences option. You can then copy the output and paste it in the -p option" )
        boolean cli();
    }


    @Description("Show the preferences or modify them" )
    public void _prefs(PreferencesOptions options) {
        if (options.cli()) {
            StringBuilder sb = new StringBuilder();
            sb.append("\"");
            String del = "";
            for (Pref< ? > pref : A4Preferences.allUserPrefs()) {
                sb.append(del).append(pref.id).append("=").append(pref.get());
                del = ",";
            }
            sb.append("\"");
            out.println(sb);
        } else {
            for (Pref< ? > pref : A4Preferences.allPrefs()) {
                out.printf("%-30s %-50s %s%n", pref.id, pref.title, pref.get());
            }
        }
    }



    @Description("Show the list of solvers" )
    @Arguments(
               arg = {} )
    interface SolverOptions extends Options {

        @Description("Show the solvers that are not available on this platform" )
        boolean unlinked();

        @Description("Show a list of names" )
        boolean list();
    }


    @Description("Show the list of solvers" )
    public void _solvers(SolverOptions options) {
        if (!options.list()) {
            out.printf("OS Platform       %s%n", NativeCode.platform);
            out.printf("Java platform     %s/%s/%n", System.getProperty("os.name"), System.getProperty("os.arch"), System.getProperty("os.version"));
        }

        List<SATFactory> list = SATFactory.getSolvers();
        if (!options.unlinked())
            list = list.stream().filter(SATFactory::isPresent).collect(Collectors.toList());

        BiConsumer<Integer,SATFactory> set;
        if (options.list()) {
            set = (row, ss) -> {
                if (row >= 0)
                    System.out.println(ss);
            };
        } else {
            Table table = new Table(list.size() + 1, 5, 1);
            table.set(0, 0, "id", "description", "type", "attributes", "diagnostic");
            set = (row, ss) -> {
                if (row < 0)
                    System.out.println(table);
                else {
                    table.set(row, 0, ss.id());
                    table.set(row, 1, wrap(ss.getDescription().orElse("")));
                    List<String> attrs = new ArrayList<>();
                    table.set(row, 2, ss.type());
                    table.set(row, 3, ss.attributes());

                    String check = ss.check();
                    if (check != null)
                        table.set(row, 4, wrap(check));
                }
            };
        }

        int r = 1;
        for (SATFactory o : list) {
            boolean available = o.isPresent();
            if (options.unlinked() || available) {
                set.accept(r, o);
                r++;
            }
        }
        set.accept(-1, null);
    }

    private String wrap(String description) {
        if (description == null)
            return "";
        StringBuilder sb = new StringBuilder(description);
        justif.wrap(sb);
        return sb.toString();
    }


    @Arguments(
               arg = {} )
    @Description("Show all the native solvers for all supported platforms" )
    interface NativeOptions extends Options {

    }

    @Description("Show all the native solvers for all supported platforms" )
    public void _natives(NativeOptions options) {
        List<SATFactory> allSolvers = SATFactory.getAllSolvers();
        int FIXED = 4;
        Table table = new Table(allSolvers.size() + 1, NativeCode.platforms.length + FIXED, 1);
        int r, c;

        c = table.set(0, 0, "id", "description", "type", "attributes");

        for (Platform p : NativeCode.platforms) {
            table.set(0, c, p.toString() + (NativeCode.platform == p ? "**" : ""));
            c++;
        }

        r = 1;
        for (SATFactory solver : allSolvers) {
            c = table.set(r, 0, solver.id(), wrap(solver.getDescription().orElse(null)), solver.type(), solver.attributes());

            String libraries[] = solver.getLibraries();
            String executables[] = solver.getExecutables();

            for (Platform platform : NativeCode.platforms) {
                NativeCode.clearCache();
                StringBuilder sb = new StringBuilder();
                String del = "";
                boolean foundOne = false;
                for (String library : libraries) {
                    Optional<File> libFile = platform.getLibrary(library);
                    if (libFile.isPresent()) {
                        sb.append(del).append(libFile.get().getName());
                        del = "\n";
                        foundOne = true;
                    }
                }
                if (foundOne) {
                    for (String library : libraries) {
                        Optional<File> libFile = platform.getLibrary(library);
                        if (!libFile.isPresent()) {
                            sb.append(del).append(library).append(" [missing]");
                        }
                    }
                }
                foundOne = false;
                for (String executable : executables) {
                    Optional<File> exeFile = platform.getExecutable(executable);
                    if (exeFile.isPresent()) {
                        sb.append(del).append(exeFile.get().getName());
                        del = "\n";
                        foundOne = true;
                    }
                }
                if (foundOne) {
                    for (String executable : executables) {
                        Optional<File> exeFile = platform.getExecutable(executable);
                        if (!exeFile.isPresent()) {
                            sb.append(del).append(executable).append(" [missing]");
                        }
                    }
                }

                if (sb.toString().length() > 0) {
                    justif.wrap(sb);
                    table.set(r, c, sb);
                }
                c++;
            }
            r++;
        }
        out.println(table);
    }


    @Description("Show help information about the available sub commands" )
    @Arguments(
               arg = {
                      "[sub-cmd]"
               } )
    interface HelpOptions extends Options {

    }

    @Description("Show all the native solvers for all supported platforms" )
    public void __help(HelpOptions options) {
        CommandLine cl = new CommandLine(this);

        Justif j = new Justif(80);
        try (Formatter f = j.formatter()) {

            cl.help(f, this);

            if (options == null || options._arguments().isEmpty()) {
                for (Object target : mains) {
                    if (target == this)
                        continue;

                    for (Entry<String,Method> e : cl.getCommands(target).entrySet()) {
                        if (e.getValue().getName().startsWith("__"))
                            continue;

                        Description d = e.getValue().getAnnotation(Description.class);
                        String desc = " ";
                        if (d != null)
                            desc = d.value();

                        f.format("  %s\t0-\t1%s %n", e.getKey(), desc);
                    }
                    f.format("%n");
                }
            } else {
                List<String> _arguments = options._arguments();
                String subcommand = _arguments.remove(0);
                for (Object target : mains) {
                    Map<String,Method> commands = cl.getCommands(target);
                    if (commands.containsKey(subcommand)) {
                        cl.help(f, target, subcommand);
                    }
                }
            }
        } catch (Exception e) {
            e.printStackTrace();
        }
        out.println(j.wrap());
    }


    private List<Object> getMains(AlloyContext context, CommandLine cl) {
        List<Object> result = new ArrayList<>();
        result.add(this);

        ParameterMap header = getHeaderMap("Provide-Capability");
        log.debug("Provide-Capability {}", header);
        header.entrySet().stream().filter(e -> e.getKey().startsWith(AlloyMain.NAMESPACE)).forEach(e -> {
            try {
                Attributes attrs = e.getValue();
                String fqn = attrs.get(AlloyMain.FQN);
                if (fqn == null)
                    throw new RuntimeException("Expected a fqn in the capability " + e);

                Class< ? > mainClass = AlloyDispatcher.class.getClassLoader().loadClass(fqn);
                AlloyMain alloyMain = mainClass.getAnnotation(AlloyMain.class);
                if (alloyMain == null)
                    throw new RuntimeException("Expected an AlloyMain annotation on " + fqn);

                Object instance = getInstance(context, e, mainClass);
                log.debug("found command provider {} -> {}", fqn, instance);
                result.add(instance);
            } catch (ClassNotFoundException e1) {
                throw new RuntimeException("In capability " + e + ", the fqn cannot be located as class in the current JAR: " + e1);
            }
        });
        return result;
    }

    private Object getInstance(AlloyContext context, Entry<String,Attributes> e, Class< ? > mainClass) {
        try {
            return mainClass.getConstructor(AlloyContext.class).newInstance(context);
        } catch (NoSuchMethodException | SecurityException | InstantiationException | IllegalAccessException | IllegalArgumentException | InvocationTargetException e1) {
            try {
                return mainClass.getConstructor().newInstance();
            } catch (InstantiationException | IllegalAccessException | IllegalArgumentException | InvocationTargetException | NoSuchMethodException | SecurityException e2) {
                throw new RuntimeException("Capability " + e + " specifies class " + mainClass + " but that class has no default constructor nor one that takes AlloyContext");
            }
        }
    }

    private ParameterMap getHeaderMap(String name) {
        return getManifest().map(m -> new ParameterMap(m.getMainAttributes().getValue(name))).orElse(new ParameterMap());
    }

    private String getVersion() {
        return getManifest().map(m -> m.getMainAttributes().getValue("Bundle-Version")).orElse("0.0.0.unknown");
    }

    private Optional<Manifest> getManifest() {
        if (manifest != null)
            return manifest;

        try {
            Enumeration<URL> e = AlloyDispatcher.class.getClassLoader().getResources("META-INF/MANIFEST.MF");

            while (e.hasMoreElements()) {
                URL nextElement = e.nextElement();
                Manifest manifest = new Manifest(nextElement.openStream());
                java.util.jar.Attributes mainAttributes = manifest.getMainAttributes();
                String bsn = mainAttributes.getValue("Bundle-SymbolicName");
                if ("org.alloytools.alloy.dist".equals(bsn)) {
                    return this.manifest = Optional.of(manifest);
                }
            }
            return Optional.empty();
        } catch (IOException e) {
            log.error("No Manifest found {}", e, e);
            return Optional.empty();
        }
    }


    static final Pattern TARGET_P = Pattern.compile("\\s*(?<name>[^=]+)\\s*=\\s*(?<level>off|trace|debug|info|warn|error)\\s*");

    public void setslf4j(Levels deflt, String... targets) {
        System.setProperty("org.slf4j.simpleLogger.defaultLogLevel", deflt.toString());
        if (targets != null)
            for (String target : targets) {
                Matcher m = TARGET_P.matcher(target);
                if (m.matches()) {
                    String key = m.group("name");
                    Levels level = Levels.valueOf(m.group("level"));
                    System.setProperty("org.slf4j.simpleLogger.log." + key, level.toString());
                } else {
                    System.err.println("invalid slf4j target definition " + target + ", expect " + TARGET_P);
                }
            }
    }

    /**
     * Load the extensions from the home directory
     *
     * @param hom
     */

    void loadExtensions(File extensions) {
        A4Solution.addTransformers(SATFactory.extensions);
        if (!extensions.isDirectory())
            return;

        for (File f : extensions.listFiles()) {
            Properties p = new Properties();
            String name = f.getName().replaceAll("\\..*", "");
            try (FileInputStream in = new FileInputStream(f)) {
                p.load(in);
                ExternalFactory externalFactory = new ExternalFactory(name, p);
                String check = externalFactory.check();
                if (check == null) {
                    SATFactory.extensions.add(externalFactory);
                } else {
                    error("cannot load extension at %s: %s", f, check);
                }
            } catch (FileNotFoundException e) {
                // can't happen
                e.printStackTrace();
            } catch (Exception e) {
                log.error("failed to load extension {}, {}", f.getAbsolutePath(), e, e);
            }
        }
    }

    public static class ExternalFactory extends SATFactory {

        static final long serialVersionUID = 1L;
        final String      id;
        final String      executable;
        final String      description;
        final String      cnf;
        final boolean     maxsat;
        final boolean     prover;
        final String[]    options;

        public ExternalFactory(String id, Properties p) {
            this.id = id;

            String executable = p.getProperty("executable");
            if (executable.indexOf(File.separatorChar) >= 0) {
                this.executable = IO.getFile(executable).getAbsolutePath();
            } else {
                this.executable = executable;
            }
            cnf = p.getProperty("cnf", null);
            description = p.getProperty("description");
            maxsat = p.getProperty("maxsat") != null;
            prover = p.getProperty("prover") != null;
            String options = p.getProperty("options");
            if (options != null) {
                this.options = Strings.splitQuoted(options, " \t\n").toArray(EMPTY);
            } else {
                this.options = EMPTY;
            }
        }

        @Override
        public String id() {
            return id;
        }

        @Override
        public SATSolver instance() {
            return new ExternalSolver(this.executable, this.cnf, true, this.options);
        }

        @Override
        public boolean prover() {
            return prover;
        }

        @Override
        public boolean maxsat() {
            return maxsat;
        }

        @Override
        public Optional<String> getDescription() {
            return Optional.ofNullable(description);
        }

        @Override
        public String toString() {
            return id() + "[extension=" + executable + "]";
        }

        @Override
        public String type() {
            return "extension";
        }
    }

}
