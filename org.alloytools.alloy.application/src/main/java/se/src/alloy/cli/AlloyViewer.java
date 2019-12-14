package se.src.alloy.cli;

import edu.mit.csail.sdg.alloy4viz.VizGUI;

import java.util.List;

public class AlloyViewer implements FileRunner {

  public static AlloyViewer create() {
    return new AlloyViewer();
  }

  public void run(List<String> files) {
    files.forEach(this::runOne);
  }

  private void runOne(String filename) {
    new VizGUI(false, filename, null);
  }
}
