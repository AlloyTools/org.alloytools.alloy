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

import java.util.List;

public class AlloyChecker implements FileRunner {
  private final Config configFile;
  private final A4Reporter reporter;

  private AlloyChecker(Config configFile, A4Reporter reporter) {
    this.configFile = configFile;
    this.reporter = reporter;
  }

  public static AlloyChecker fromConfigFile(Config configFile) {
    return new AlloyChecker(configFile, new A4Reporter());
  }

  public void run(List<String> files) {
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
          switch (this.configFile.verbosity()) {
            case HIGH:
              Printer.log(cmd.toString() + "... ");
              break;
            case LOW:
              String name = cmd.nameExpr.toString();
              if (name.equals("true")) {
                Printer.log("Run {}... ");
              } else {
                Printer.log(name + "...");
              }
              break;
          }
          A4Solution ans =
              TranslateAlloyToKodkod.execute_command(reporter, allReachableSigs, cmd, options);
          switch (this.configFile.verbosity()) {
            case HIGH:
              if (ans.satisfiable()) {
                Printer.success("Satisfied!");
              } else {
                Printer.error("Could Not Satisfy!");
              }
              break;
            case LOW:
              if (ans.satisfiable()) {
                Printer.success("SAT");
              } else {
                Printer.error("UNSAT");
              }
              break;
          }
          System.out.println();
        });
  }
}
