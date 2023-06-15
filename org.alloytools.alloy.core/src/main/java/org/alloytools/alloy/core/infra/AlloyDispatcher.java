package org.alloytools.alloy.core.infra;


import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.net.URL;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Formatter;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.function.BiConsumer;
import java.util.jar.Manifest;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import org.alloytools.alloy.context.api.AlloyContext;
import org.alloytools.alloy.core.infra.NativeCode.Platform;
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
import aQute.libg.parameters.Attributes;
import aQute.libg.parameters.ParameterMap;
import aQute.service.reporter.Reporter;
import edu.mit.csail.sdg.alloy4.A4Preferences;
import edu.mit.csail.sdg.alloy4.A4Preferences.Pref;
import edu.mit.csail.sdg.translator.A4Options.SatSolver;

/**
 * Since the Alloy code is used for many different situations, we do not assume
 * we know how the world looks like. This class uses the AlloyMain annotation to
 * find any class that can be called from the command line that was added to the
 * distribution jar.
 *
 */
@Description("The Alloy command line interpreter" )
public class AlloyDispatcher extends Env {

    PrintStream          out = System.out;
    PrintStream          err = System.err;
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
                    report(System.err);
                    return;
                }
            }
            error("no such command %s, use help to get a full list", subcommand);
            __help(null);
            report(System.err);

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
            context = new AlloyContext() {

                @Override
                public boolean isDebug() {
                    return options.debug();
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

        List<SatSolver> list = SatSolver.values();
        if (!options.unlinked())
            list = list.stream().filter(SatSolver::present).collect(Collectors.toList());

        BiConsumer<Integer,SatSolver> set;
        if (options.list()) {
            set = (row, ss) -> {
                if (row >= 0)
                    System.out.println(ss);
            };
        } else {
            Table table = new Table(list.size() + 1, 5, 1);
            table.set(0, 0, "id");
            table.set(0, 1, "libname");
            table.set(0, 2, "external");
            table.set(0, 3, "description");
            table.set(0, 4, "exception");
            set = (row, ss) -> {
                if (row < 0)
                    System.out.println(table);
                else {
                    table.set(row, 0, ss.id());
                    if (ss.libname != null) {
                        table.set(row, 1, ss.libname);
                        String mapLibraryName = System.mapLibraryName(ss.libname);
                        File exec = NativeCode.findexecutable(mapLibraryName);
                        if (exec != null) {
                            if (ss.libname != null)
                                try {
                                    System.loadLibrary(ss.libname);
                                } catch (java.lang.UnsatisfiedLinkError ee) {
                                    table.set(row, 4, ee.toString());
                                }
                        }
                    }
                    if (ss.external() != null)
                        table.set(row, 2, ss.external());
                    table.set(row, 3, ss.toString());
                }
            };
        }

        int r = 1;
        for (SatSolver o : list) {
            boolean available = o.present();
            if (options.unlinked() || available) {
                set.accept(r, o);
                r++;
            }
        }
        set.accept(-1, null);
    }

    @Arguments(
               arg = {} )
    @Description("Show all the native solvers for all supported platforms" )
    interface NativeOptions extends Options {

    }

    @Description("Show all the native solvers for all supported platforms" )
    public void _natives(NativeOptions options) {
        Table table = new Table(SatSolver.values().size() + 1, NativeCode.platforms.length + 1, 1);
        int r, c = 1;
        for (Platform p : NativeCode.platforms) {
            table.set(0, c++, p.toString());
        }
        r = 1;
        for (SatSolver solver : SatSolver.values()) {
            table.set(r, 0, solver.toString());
            c = 1;
            for (Platform p : NativeCode.platforms) {
                StringBuilder sb = new StringBuilder();
                if (solver.libname != null) {
                    String mapLibraryName = p.mapLibrary(solver.libname);
                    File exec = NativeCode.findexecutable(p, mapLibraryName);
                    if (exec != null && exec.isFile()) {
                        table.set(r, c, mapLibraryName);
                    }
                }
                if (solver.external() != null) {
                    String mapExeName = p.mapExe(solver.external());
                    File exec = NativeCode.findexecutable(p, mapExeName);
                    if (exec != null && exec.isFile()) {
                        table.set(r, c, mapExeName);
                    }
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
                return mainClass.newInstance();
            } catch (InstantiationException | IllegalAccessException e2) {
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
            URL resource = AlloyDispatcher.class.getResource("/META-INF/MANIFEST.MF");
            if (resource == null)
                return Optional.empty();

            Manifest manifest = new Manifest(resource.openStream());
            return this.manifest = Optional.of(manifest);
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
}
