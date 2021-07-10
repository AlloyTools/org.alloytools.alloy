package se.src.alloy.cli;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.atomic.AtomicReference;

public class Args {
  public final Config configFile;
  private List<String> files;
  private final Boolean watch;

  private Args(Config configFile, List<String> files, Boolean watch) {
    this.configFile = configFile;
    this.files = files;
    this.watch = watch;
  }

  public static Args parse(List<String> args) throws IOException {
    String configFile = parse_configFile(args);
    Boolean watch = parse_watchFlag(args);
    List<String> files = parse_files(args);
    return new Args(Config.fromFile(configFile), files, watch);
  }

  private static Boolean parse_watchFlag(List<String> args) {
    AtomicReference<Boolean> watch = new AtomicReference<Boolean>();
    watch.set(Config.DEFAULT_WATCH_MODE);
    args.forEach(
            x -> {
              String flag = flag(x);
              if (flag.equals("--watch")) {
                watch.set(true);
              }
            });
    return watch.get();
  }

  private static List<String> parse_files(List<String> args) {
    ArrayList<String> files = new ArrayList<>(args);
    files.removeIf(Args::isFlag);
    return files;
  }

  private static boolean isFlag(String x) {
    return x.contains("=");
  }

  private static String parse_configFile(List<String> args) {
    AtomicReference<String> file = new AtomicReference<String>();
    file.set(Config.DEFAULT_CONFIG_FILE);
    args.forEach(
        x -> {
          String flag = flag(x);
          if (flag.equals("--config")) {
            String value = value(x);
            file.set(value);
          }
        });
    return file.get();
  }

  private static String flag(String x) {
    return x.split("=")[0];
  }

  private static String value(String x) {
    return x.split("=")[1];
  }

  public Config configFile() {
    return this.configFile;
  }

  public List<String> files() {
    return this.files;
  }

  public Boolean watch() {
    return this.watch;
  }
}
