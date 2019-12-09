package se.src.alloy.cli;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

import java.io.File;
import java.util.List;

public class AlloyRenderer {
  public static final String DEFAULT_GRAPH_FOLDER = "./graphs/";
  private final Config configFile;
  private final A4Reporter reporter;

  private AlloyRenderer(Config configFile, A4Reporter reporter) {
    this.configFile = configFile;
    this.reporter = reporter;
  }

  public static AlloyRenderer fromConfigFile(Config configFile) {
    return new AlloyRenderer(configFile, new A4Reporter());
  }

  public void run(List<String> files) {
    File file = new File(DEFAULT_GRAPH_FOLDER);
    file.mkdirs();
    files.forEach(this::runOne);
  }

  private void runOne(String filename) {
    if (this.configFile.verbosity() == Config.Verbosity.HIGH) {
      Printer.log("Starting at file " + filename);
      System.out.println();
    }

    Module world = CompUtil.parseEverything_fromFile(reporter, null, filename);
    A4Options options = new A4Options();
    options.solver = A4Options.SatSolver.SAT4J;

    ConstList<Command> allCommands = world.getAllCommands();
    ConstList<Sig> allReachableSigs = world.getAllReachableSigs();

    allCommands.forEach(
        cmd -> {
          A4Solution ans =
              TranslateAlloyToKodkod.execute_command(reporter, allReachableSigs, cmd, options);
          String name = name(cmd);
          Printer.log(name + "...");
          if (ans.satisfiable()) {
            String fileName = DEFAULT_GRAPH_FOLDER + name + ".xml";
            ans.writeXML(fileName);
            Printer.success("DRAWN");
          } else {
            Printer.error("SKIP");
          }
          System.out.println();
        });
  }

  private String name(Command cmd) {
    if (cmd.nameExpr.toString().equals("true")) {
      return "general";
    } else {
      return cmd.nameExpr.toString();
    }
  }
}
