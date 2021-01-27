package edu.mit.csail.sdg.alloy4whole;


import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.OptionGroup;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

public class SimpleMain {

    static private A4Options options;
    private static long      start_time = 0;

    private static final class SimpleReporter extends A4Reporter {

        private Logger     LOGGER = LoggerFactory.getLogger(SimpleMain.class);

        private int        cmd_index;
        private boolean    outcome;
        private String     cmd_name;
        private boolean    cmd_type;
        private boolean    expected;
        private int        overall;
        private long       total_time;
        private String     filename;
        private A4Solution solution;

        public SimpleReporter() throws IOException {
        }

        @Override
        public void debug(String msg) {
            if (System.getProperty("debug", "no").equals("yes"))
                LOGGER.debug(msg);
        }

        @Override
        public void parse(String msg) {
            debug(msg);
        }

        @Override
        public void typecheck(String msg) {
            debug(msg);
        }

        public void cmd_index(int i) {
            cmd_index = i;
        }

        public void info(String msg) {
            LOGGER.info(msg);
        }

        @Override
        public void warning(ErrorWarning msg) {
            LOGGER.warn(msg.msg);
        }

        @Override
        public void scope(String msg) {
            debug(msg);
        }

        @Override
        public void bound(String msg) {
            debug(msg);
        }

        @Override
        // [HASLab] trace + decompose params
        public void translate(String solver, int bitwidth, int maxseq, int mintrace, int maxtrace, int skolemDepth, int symmetry, String strat) {
            info("Solver=" + solver + " Steps=" + mintrace + ".." + maxtrace + " Bitwidth=" + bitwidth + " MaxSeq=" + maxseq + " Symmetry=" + (symmetry > 0 ? ("" + symmetry) : "OFF") + " Mode=" + strat + "\n"); // [HASLab]
        }

        int totalVars = 0, totalPvars = 0, totalClauses = 0, lastStep = 0;

        @Override
        public void solve(int plength, int pVars, int vars, int clauses) {
            lastStep = plength;
            totalVars += vars;
            totalPvars += pVars;
            totalClauses += clauses;
            info("Step " + plength + ". " + vars + " vars. " + pVars + " primary vars. " + clauses + " clauses.\n");
        }

        @Override
        public void resultCNF(String filename) {
        }

        @Override
        public void resultSAT(Object command, long solvingTime, Object solution) {
            if (!(command instanceof Command))
                return;
            Command cmd = (Command) command;
            outcome = true;
            total_time = System.currentTimeMillis() - start_time;
            expected = cmd.expects == 1;
            cmd_name = cmd.label;
            cmd_type = cmd.check;
            overall = cmd.overall;
            filename = ((A4Solution) solution).getOriginalFilename();
            this.solution = (A4Solution) solution;
            StringBuilder sb = new StringBuilder();
            sb.append(cmd.check ? "   Counterexample found. " : "   Instance found. ");
            if (cmd.check)
                sb.append("Assertion is invalid");
            else
                sb.append("Predicate is consistent");
            if (cmd.expects == 0)
                sb.append(", contrary to expectation");
            else if (cmd.expects == 1)
                sb.append(", as expected");
            sb.append(". " + solvingTime + "ms.\n\n");
            info(sb.toString());
            info(lastStep + " steps. " + totalVars + ", " + totalPvars + " primary vars, " + totalClauses + " clauses (total).\n");
            info(outcome());
        }

        @Override
        public void resultUNSAT(Object command, long solvingTime, Object solution) {
            if (!(command instanceof Command))
                return;
            Command cmd = (Command) command;
            outcome = false;
            total_time = System.currentTimeMillis() - start_time;
            expected = cmd.expects == 0;
            cmd_name = cmd.label;
            cmd_type = cmd.check;
            overall = cmd.overall;
            filename = ((A4Solution) solution).getOriginalFilename();
            this.solution = null;
            StringBuilder sb = new StringBuilder();
            sb.append(cmd.check ? "   No counterexample found." : "   No instance found.");
            if (cmd.check)
                sb.append(" Assertion may be valid");
            else
                sb.append(" Predicate may be inconsistent");
            if (cmd.expects == 1)
                sb.append(", contrary to expectation");
            else if (cmd.expects == 0)
                sb.append(", as expected");
            sb.append(". " + solvingTime + "ms.\n\n");
            info(sb.toString());
            info(outcome());
        }

        private String outcome() {
            StringBuilder sb = new StringBuilder("OUTCOME (");
            sb.append("(file " + filename + ") ");
            sb.append("(index " + cmd_index + ") ");
            sb.append("(ms " + total_time + ") ");
            sb.append("(cmd " + (cmd_type ? "check" : "run") + ") ");
            sb.append("(label " + cmd_name + ") ");
            sb.append("(scope " + overall + ") ");
            sb.append("(outcome " + (outcome ? "SAT" : "UNSAT") + ") ");
            sb.append("(engine " + options.solver.toString() + ") ");
            sb.append("(as_expected " + expected + "))\n");
            if (clargs.hasOption('o') && solution != null) {
                StringWriter wr = new StringWriter();
                try {
                    solution.writeXML(this, new PrintWriter(wr), new ArrayList<Func>(), new HashMap<String,String>());
                } catch (Err e) {
                    // TODO Auto-generated catch block
                    e.printStackTrace();
                }
                sb.append(wr.toString());
            }
            return sb.toString();
        }
    }

    private SimpleMain() {
    }

    private static Options options() {
        Options options = new Options();

        options.addOption(Option.builder("c").longOpt("command").hasArg(true).argName("command").optionalArg(false).required(false).desc("select command").build());

        options.addOption(Option.builder("v").longOpt("verbose").hasArg(false).required(false).desc("run in debug mode").build());

        options.addOption(Option.builder("o").longOpt("output").hasArg(false).required(false).desc("print full output if SAT").build());

        options.addOption(Option.builder("so").longOpt("solver-options").hasArg(true).required(false).desc("additional solver-specific options").build());

        options.addOption(Option.builder().longOpt("cli").hasArg(false).desc("force CLI mode").build());

        options.addOption(Option.builder("d").longOpt("decomposed").hasArg(true).argName("threads").optionalArg(true).required(false).desc("run in decomposed mode").build());

        OptionGroup g = new OptionGroup();
        g.addOption(Option.builder("m").longOpt("miniSAT").hasArg(false).desc("select miniSAT bounded solver").build());
        g.addOption(Option.builder("g").longOpt("glucose").hasArg(false).desc("select glucose unbounded solver").build());
        g.addOption(Option.builder("s").longOpt("SAT4J").hasArg(false).desc("select SAT4J bounded solver").build());
        g.setRequired(false);

        options.addOptionGroup(g);

        return options;
    }

    static CommandLine clargs = null;

    public static void main(String[] args) throws Exception {
        try {
            CommandLineParser parser = new DefaultParser();
            clargs = parser.parse(options(), args, true);
        } catch (ParseException exp) {
            System.err.println("Parsing failed.  Reason: " + exp.getMessage());
            HelpFormatter formatter = new HelpFormatter();
            formatter.printHelp("electrum [options] [FILE]", options());
            return;
        }

        // if a single cli arg, then must be file name, open gui
        if (args.length <= 1 && !clargs.hasOption("cli"))
            SimpleGUI.main(args);
        else {

            if (clargs.hasOption("v"))
                System.setProperty("debug", "yes");

            // set the temp files
            //                    copyFromJAR();

            final SimpleReporter rep = new SimpleReporter();
            String filename = args[args.length - 1];
            try {
                rep.info("Parsing " + filename + ".\n");
                Module world = CompUtil.parseEverything_fromFile(rep, null, filename);
                List<Command> cmds = world.getAllCommands();
                options = new A4Options();
                options.originalFilename = filename;
                options.solver = A4Options.SatSolver.MiniSatJNI;
                if (clargs.hasOption("SAT4J"))
                    options.solver = A4Options.SatSolver.SAT4J;
                else if (clargs.hasOption("glucose"))
                    options.solver = A4Options.SatSolver.GlucoseJNI;

                if (clargs.hasOption("decomposed"))
                    options.decomposed_mode = 1;
                if (clargs.getOptionValue("decomposed") != null)
                    options.decomposed_threads = Integer.valueOf(clargs.getOptionValue("decomposed"));
                else
                    options.decomposed_mode = 0;

                int i0 = 0, i1 = cmds.size();
                if (clargs.hasOption("command")) {
                    i0 = Integer.valueOf(clargs.getOptionValue("command"));
                    i1 = i0 + 1;
                } else {
                    rep.info("Running all commands.");
                }
                for (int i = i0; i < i1; i++) {
                    Command c = cmds.get(i);
                    rep.cmd_index(i);
                    rep.info("Executing \"" + c + "\"\n");
                    options.skolemDepth = 2;
                    start_time = System.currentTimeMillis();
                    TranslateAlloyToKodkod.execute_commandFromBook(rep, world.getAllReachableSigs(), c, options);
                }
                rep.info("Shutting down.");
                System.exit(0);
            } catch (Throwable ex) {
                rep.info("An error occurred.");
                rep.debug("\n\nException: " + ex);
            }
        }
    }

}
