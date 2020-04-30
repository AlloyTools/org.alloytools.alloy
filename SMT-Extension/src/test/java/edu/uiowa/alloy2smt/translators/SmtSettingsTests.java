package edu.uiowa.alloy2smt.translators;

import edu.uiowa.smt.printers.SmtLibPrinter;
import edu.uiowa.smt.smtAst.SmtSettings;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertTrue;

public class SmtSettingsTests
{
  @Test
  void settings()
  {
    SmtSettings smtSettings = SmtSettings.getInstance();
    smtSettings.putSolverOption("tlimit", "5000");
    smtSettings.putSolverOption(SmtSettings.PRODUCE_UNSAT_CORES, "true");

    SmtLibPrinter printer = new SmtLibPrinter(smtSettings);
    printer.visit(smtSettings);
    String script = printer.getSmtLib();
    assertTrue(script.contains("(set-option :tlimit 5000)\n"));
    assertTrue(script.contains("(set-option :produce-unsat-cores true)\n"));
  }
}

