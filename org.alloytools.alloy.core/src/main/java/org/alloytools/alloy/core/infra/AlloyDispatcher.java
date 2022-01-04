package org.alloytools.alloy.core.infra;


import java.io.IOException;
import java.io.PrintStream;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.net.URL;
import java.util.Arrays;
import java.util.Formatter;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.TreeMap;
import java.util.jar.Manifest;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import org.alloytools.alloy.context.api.AlloyContext;
import org.alloytools.alloy.infrastructure.api.AlloyMain;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import aQute.lib.getopt.Arguments;
import aQute.lib.getopt.CommandLine;
import aQute.lib.getopt.Description;
import aQute.lib.getopt.Options;
import aQute.lib.io.IO;
import aQute.lib.justif.Justif;
import aQute.lib.strings.Strings;
import aQute.libg.parameters.Attributes;
import aQute.libg.parameters.ParameterMap;
import aQute.libg.reporter.ReporterAdapter;
import edu.mit.csail.sdg.alloy4.A4Preferences;
import edu.mit.csail.sdg.alloy4.A4Preferences.Pref;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Options.SatSolver;

/**
 * Since the Alloy code is used for many different situations, we do not assume
 * we know how the world looks like. This class uses the AlloyMain annotation to
 * find any class that can be called from the command line that was added to the
 * distribution jar.
 *
 */
public class AlloyDispatcher extends ReporterAdapter {

    final static Logger log = LoggerFactory.getLogger(AlloyDispatcher.class);
    PrintStream         out = System.out;
    PrintStream         err = System.err;
    AlloyContext        context;
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

        CommandLine cl = options._command();
        AlloyContext context = getContext(options);
        Map<String,MainDef> mains = getMains(context, cl);

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

            log.info("selected main {} is with arguments {}", selected, arguments);

            String execute = cl.execute(selected.instance, selected.name, arguments);
            if (execute != null) {
                err.println(execute);
            }

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
    }


    public void _solvers(SolverOptions options) {
        StringBuilder sb = new StringBuilder();
        for (SatSolver o : A4Options.SatSolver.values()) {
            out.printf("%s%n", o);
        }
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
        Map<String,MainDef> mains = getMains(context, cl);
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


    private Map<String,MainDef> getMains(AlloyContext context, CommandLine cl) {
        Map<String,MainDef> result = new TreeMap<>();
        localCommands(cl, result);
        globalCommands(context, result);
        return result;
    }

    private void globalCommands(AlloyContext context, Map<String,MainDef> result) {
        ParameterMap header = getHeader("Provide-Capability");

        header.entrySet().stream().filter(e -> e.getKey().startsWith(AlloyMain.NAMESPACE)).forEach(e -> {
            try {
                Attributes attrs = e.getValue();
                String fqn = attrs.get(AlloyMain.FQN);
                if (fqn == null)
                    throw new RuntimeException("Expected a fqn in the capability " + e);

                Class< ? > mainClass = AlloyDispatcher.class.getClassLoader().loadClass(fqn);
                AlloyMain mainAnn = mainClass.getAnnotation(AlloyMain.class);
                if (mainAnn != null) {
                    Object instance = getInstance(context, e, mainClass);
                    MainDef main = new MainDef(instance, mainAnn.name(), mainAnn.isDefault());
                    result.put(main.name, main);
                    log.debug("found main class {}", main);
                } else {
                    throw new RuntimeException("Main class " + mainClass + " is listed in capability " + e + " but does not have an AlloyMain annotation");
                }
            } catch (ClassNotFoundException e1) {
                throw new RuntimeException("In capability " + e + ", the fqn cannot be located as class in the current JAR: " + e1);
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

    private ParameterMap getHeader(String name) {
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

    public static void setslf4j(Levels deflt, String... targets) {
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
