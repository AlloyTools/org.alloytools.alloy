package se.src.alloy.cli;

import edu.mit.csail.sdg.alloy4.Version;

import java.io.IOException;
import java.util.Arrays;
import java.util.List;

public final class CLI {
  public static void main(String[] rawArgs) throws IOException, InterruptedException {
    long startTime = System.nanoTime();
    Printer.log("Alloy " + Version.getShortversion());
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

  private static void dispatch(SubCommand subCommand, List<String> rest)
      throws IOException, InterruptedException {
    Args args = Args.parse(rest);

    FileRunner cmd = pickCommand(subCommand, args);

    if (args.watch()) {
      Watcher.run(args, cmd);
    } else {
      cmd.run(args.files());
    }
  }

  private static FileRunner pickCommand(SubCommand subCommand, Args args) {
    switch (subCommand) {
      case VIEW:
        return AlloyViewer.create();

      case RENDER:
        return AlloyRenderer.fromConfigFile(args.configFile());

      case CHECK:
      default:
        return AlloyChecker.fromConfigFile(args.configFile());
    }
  };

  public enum SubCommand {
    CHECK,
    RENDER,
    VIEW
  }
}
