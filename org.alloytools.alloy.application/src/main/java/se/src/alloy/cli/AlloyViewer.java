package se.src.alloy.cli;

import edu.mit.csail.sdg.alloy4viz.VizGUI;

import java.util.List;

public class AlloyViewer {

  public static void run(List<String> files) {
    files.forEach(AlloyViewer::runOne);
  }

  private static void runOne(String filename) {
    new VizGUI(false, filename, null);
  }
}
