package se.src.alloy.cli;

import javax.print.PrintException;
import java.io.IOException;
import java.nio.file.*;
import java.util.List;

import static java.nio.file.StandardWatchEventKinds.ENTRY_MODIFY;

public class Watcher {
  public static void run(Args args, FileRunner cmd) throws IOException, InterruptedException {
    Path cwd = Paths.get("");

    WatchService watcher = cwd.getFileSystem().newWatchService();

    cwd.register(watcher, ENTRY_MODIFY);

    WatchKey watckKey = watcher.take();

    while (true) {
      List<WatchEvent<?>> events = watckKey.pollEvents();
      for (WatchEvent event : events) {
        String file = event.context().toString();
        if (file.contains(".als") & !file.contains(".sw") & event.kind() == ENTRY_MODIFY) {
          Printer.log("Running " + file + "...");
          Printer.newline();
          try {
            cmd.run(args.files());
          } catch (Exception e) {
            Printer.log("");
            Printer.error("Something went wrong!");
            Printer.newline();
            e.printStackTrace();
            Printer.newline();
          }
        }
      }
      Thread.sleep(500);
    }
  }
}
