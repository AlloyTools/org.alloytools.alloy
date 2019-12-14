package se.src.alloy.cli;

import java.time.Instant;
import java.time.LocalDateTime;
import java.time.ZoneId;
import java.time.format.DateTimeFormatter;

public class Printer {

  public static final String COLOR_RESET = "\033[0m";
  public static final String COLOR_BLUE = "\033[1;34m";
  static final String COLOR_GREEN = "\033[0;32m";
  static final String COLOR_RED_BOLD = "\033[1;31m";

  public static void log(String s) {
    String sep = " | ";
    Instant now = Instant.now();
    String date =
        LocalDateTime.ofInstant(now, ZoneId.systemDefault())
            .format(DateTimeFormatter.ISO_LOCAL_TIME)
            .substring(0, 13);
    System.out.print(COLOR_BLUE + date + COLOR_RESET + sep + s);
  }

  public static void append(String s) {
    System.out.print(s);
  }

  public static void success(String t) {
    System.out.print(Printer.COLOR_GREEN + t + Printer.COLOR_RESET);
  }

  public static void error(String s) {
    System.out.print(Printer.COLOR_RED_BOLD + s + Printer.COLOR_RESET);
  }

  public static void newline() {
    System.out.println();
  }
}
