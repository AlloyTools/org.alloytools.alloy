package se.src.alloy.cli;

import java.io.IOException;
import java.util.Arrays;
import java.util.List;

public final class CLI {
  public static void main(String[] rawArgs) throws IOException {
    long startTime = System.nanoTime();
    Printer.log("Alloy Runner v0.0.1");
    Printer.newline();

    List<String> args1 = Arrays.asList(rawArgs);
    String subCommand = args1.get(0);
    List<String> rest = args1.subList(1, args1.size());

    dispatch(SubCommand.valueOf(subCommand.toUpperCase()), rest);

    long endTime = System.nanoTime();
    double delta = (endTime - startTime) / 1000.0 / 1000.0; // nano -> micro -> milli
    Printer.log("Finished in " + delta + "ms");
    Printer.newline();
  }

  private static void dispatch(SubCommand subCommand, List<String> rest) throws IOException {
    Args args = Args.parse(rest);

    switch (subCommand) {
      case CHECK:
        AlloyChecker.fromConfigFile(args.configFile()).run(args.files());
        break;

      case RENDER:
        AlloyRenderer.fromConfigFile(args.configFile()).run(args.files());
        break;

      case VIEW:
        AlloyViewer.run(args.files());
        break;
    }
  }

  public enum SubCommand {
    CHECK,
    RENDER,
    VIEW
  }
}
