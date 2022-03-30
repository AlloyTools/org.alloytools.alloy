package org.alloytools.alloy.core.infra;


import java.io.IOException;
import java.io.PrintStream;
import java.lang.reflect.Method;
import java.net.URL;
import java.util.Arrays;
import java.util.Enumeration;
import java.util.Formatter;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.TreeMap;
import java.util.jar.Manifest;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import org.allotools.services.util.Services;
import org.alloytools.alloy.core.api.Alloy;
import org.alloytools.alloy.core.api.Solver;
import org.alloytools.alloy.core.api.Visualizer;
import org.alloytools.alloy.infrastructure.api.AlloyCLI;
import org.alloytools.cli.api.CLICommand;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import aQute.lib.getopt.Arguments;
import aQute.lib.getopt.CommandLine;
import aQute.lib.getopt.Description;
import aQute.lib.getopt.Options;
import aQute.lib.io.IO;
import aQute.lib.justif.Justif;
import aQute.lib.strings.Strings;
import aQute.libg.reporter.ReporterAdapter;
import edu.mit.csail.sdg.alloy4.A4Preferences;
import edu.mit.csail.sdg.alloy4.A4Preferences.Pref;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Options.SatSolver;

/**
 * Since the Alloy code is used for many different situations, we do not assume
 * we know how the world looks like. This class uses the AlloyCLI annotation to
 * find any class that can be called from the command line that was added to the
 * distribution jar.
 *
 */
public class AlloyDispatcher extends ReporterAdapter {

    final static Logger logger = LoggerFactory.getLogger(AlloyDispatcher.class);

    PrintStream         out    = System.out;
    PrintStream         err    = System.err;
    Alloy               alloy;
    Optional<Manifest>  manifest;



    static class MainDef implements AutoCloseable {

        public final String  name;
        public final Object  instance;
        public final boolean deflt;

        public MainDef(Object instance, String name, boolean deflt) {
            this.instance = instance;
            this.name = name;
            this.deflt = deflt;
        }

        @Override
        public String toString() {
            return "MainDef [name=" + name + ", instance=" + instance + "]";
        }

        @Override
        public void close() throws Exception {
            if (instance instanceof AutoCloseable)
                IO.close((AutoCloseable) instance);
        }
    }

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

        @Description("A comma separated string with Alloy preferences. Preference id's (and their values) can be found with the `prefs` sub command. Usually enclosed in quotes to prevent the shell from breaking them up. Preferences are stored persistently." )
        String preferences();
    }

    public static void main(String[] args) {
        AlloyDispatcher dispatcher = new AlloyDispatcher();
        CommandLine cl = new CommandLine(dispatcher);
        try {
            String help = cl.execute(dispatcher, "alloy", Arrays.asList(args));
            if (help != null) {
                System.err.println(help);
            }
        } catch (Exception e) {
            dispatcher.exception(e, "invocation failed %s", e.getMessage());
        }
        dispatcher.report(System.out);
    }

    public void _alloy(BaseOptions options) throws Exception {
        if (options.debug())
            System.setProperty("debug", "yes");

        setslf4j(options.defaultLevel(Levels.error), options.log());

        this.alloy = Services.getService(Alloy.class);
        if (alloy == null)
            throw new Error("No implementation for Alloy available");

        CommandLine cl = options._command();
        Map<String,MainDef> mains = getMains(alloy, cl);

        doPreferences(options.preferences());

        try {


            List<String> arguments = options._arguments();

            MainDef selected;
            if (arguments.isEmpty()) {
                selected = mains.entrySet().stream().filter(e -> e.getValue().deflt).map(e -> e.getValue()).findAny().orElse(null);
                if (selected == null) {
                    error("invalid JAR, could not find a main that is the default and no command was given. Main classes found %s", mains);
                    return;
                }
            } else {
                String _name = arguments.remove(0);
                String name = _name.equals("help") ? "_help" : _name; // 'help' is built in but we override it
                selected = mains.entrySet().stream().filter(e -> e.getValue().name.equals(name)).map(e -> e.getValue()).findAny().orElse(null);
                if (selected == null) {
                    error("No such command: %s, available commands are %s", name, mains.keySet());
                    return;
                }
            }

            if (!isOk()) {
                return;
            }

            String help = cl.execute(selected.instance, selected.name, arguments);
            if (help != null) {
                err.println(help);
            }
        } catch (Exception e) {
            e.printStackTrace();
        } finally {
            mains.values().forEach(IO::close);
        }
    }


    @Arguments(
               arg = {} )
    @Description("Display the current version" )
    interface VersionOptions extends Options {

        @Description("Show the full major.minor.micro.qualifier version, normal it does not print the qualifier" )
        boolean full();
    }

    public void _version(VersionOptions options) {
        String version = getVersion();
        if (!options.full()) {
            int n = version.lastIndexOf('.');
            if (n > 0)
                version = version.substring(0, n);
        }
        out.println(version);
    }

    @Description("Show the preferences or modify them" )
    @Arguments(
               arg = {} )
    interface PreferencesOptions extends Options {

        @Description("Show the preferences in a comma separated format as used by the alloy `-p` preferences option. You can then copy the output and paste it in the -p option" )
        boolean cli();
    }


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

        @Description("show classic kodkod solvers" )
        boolean kodkod();
    }


    public void _solvers(SolverOptions options) {
        if (options.kodkod()) {
            for (SatSolver o : A4Options.SatSolver.values()) {
                out.printf("%s%n", o);
            }
        } else {
            Justif j = new Justif(100, 0, 3, 30, 60, 80);
            Formatter f = j.formatter();
            for (Map.Entry<String,Solver> e : alloy.getSolvers().entrySet()) {
                if (e.getKey().isEmpty())
                    continue;

                Solver solver = e.getValue();
                f.format("%s\t1%s\t2%s\t3%s\n", solver.isAvailable() ? "ok" : "x", solver.getName(), e.getKey(), solver.getDescription());
            }
            out.println(j.wrap());
        }
    }

    public void _visualizers(SolverOptions options) {
        Justif j = new Justif(120, 0, 40, 60, 80, 100);
        Formatter f = j.formatter();
        for (Visualizer e : alloy.getVisualizers()) {
            f.format("%s\t1%s\n", e.getName(), e.getDescription());
        }
        out.println(j.wrap());
    }



    @Description("Show help information about the available sub commands" )
    @Arguments(
               arg = {
                      "[sub-cmd]"
               } )
    interface HelpOptions extends Options {

    }

    public void __help(HelpOptions options) {
        List<String> arguments = options._arguments();
        CommandLine cl = options._command();
        Map<String,MainDef> mains = getMains(alloy, cl);
        Justif j = new Justif(80);
        try (Formatter f = j.formatter()) {

            if (arguments.isEmpty()) {
                cl.help(f, this, "alloy");
                f.format("Sub commands are: %s%n", mains.keySet().stream().collect(Collectors.joining(", ")).replace("_help", "help"));
                f.format("Do 'help <sub-cmd> to get more information about a particular sub command%n", mains.keySet().stream().collect(Collectors.joining(", ")));
            } else {
                for (Map.Entry<String,MainDef> e : mains.entrySet()) {
                    String name = e.getKey();
                    if (!arguments.contains(name))
                        continue;

                    MainDef main = e.getValue();
                    if (main.deflt)
                        f.format("[default]");
                    cl.help(f, main.instance, name);
                }
            }
            out.println(j.wrap());
        }
    }


    private Map<String,MainDef> getMains(Alloy context, CommandLine cl) {
        Map<String,MainDef> result = new TreeMap<>();
        localCommands(cl, result);
        globalCommands(context, result);
        return result;
    }

    private void globalCommands(Alloy context, Map<String,MainDef> result) {

        Services.getServices(CLICommand.class, context::create).forEach(cmd -> {
            AlloyCLI annotation = cmd.getClass().getAnnotation(AlloyCLI.class);
            for (String subCommand : annotation.subCommand()) {
                MainDef main = new MainDef(cmd, subCommand, annotation.isDefault());
                result.put(subCommand, main);
            }
        });
    }

    private void localCommands(CommandLine cl, Map<String,MainDef> result) {
        Map<String,Method> commands = cl.getCommands(this);
        for (Map.Entry<String,Method> e : commands.entrySet()) {
            String cmd = e.getKey();
            if (cmd.equals("alloy"))
                continue;

            MainDef md = new MainDef(this, cmd, false);
            result.put(cmd, md);
        }
    }

    final static Pattern PREF_P = Pattern.compile("\\s*(?<id>[^=]+)\\s*(=\\s*(?<value>.*)\\s*)");

    private void doPreferences(String preferences) {
        if (preferences == null)
            return;

        for (String pref : Strings.splitQuoted(preferences)) {
            Matcher m = PREF_P.matcher(pref);
            if (!m.matches()) {
                error("cannot match preferences '%s', particularly `%s`", preferences, pref);
            } else {
                String id = m.group("id");
                String value = m.group("value");
                if (value == null)
                    value = "true";

                String result = A4Preferences.set(id, value);
                if (result != null) {
                    error("Setting pref %s failed: %s", id, result);
                }
            }
        }

    }

    private String getVersion() {
        return getManifest().map(m -> m.getMainAttributes().getValue("Bundle-Version")).orElse("0.0.0.unknown");
    }

    private Optional<Manifest> getManifest() {
        if (manifest != null)
            return manifest;

        try {
            // Alloy is the only class loaded from the standard class loader ...
            Enumeration<URL> resource = Alloy.class.getClassLoader().getResources("META-INF/MANIFEST.MF");

            if (resource == null)
                return Optional.empty();

            while (resource.hasMoreElements()) {
                Manifest m = new Manifest(resource.nextElement().openStream());
                String value = m.getMainAttributes().getValue("JPM-Command");
                if (value != null)
                    return this.manifest = Optional.of(m);
            }
            return Optional.empty();
        } catch (IOException e) {
            System.err.println("No Manifest found " + e);
            return Optional.empty();
        }
    }


    static final Pattern TARGET_P = Pattern.compile("\\s*(?<name>[^=]+)\\s*=\\s*(?<level>off|trace|debug|info|warn|error)\\s*");

    public static void setslf4j(Levels deflt, String... targets) {
        System.setProperty(org.slf4j.impl.SimpleLogger.DEFAULT_LOG_LEVEL_KEY, deflt.toString());
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
