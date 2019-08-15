package edu.uiowa.alloy2smt.translators;

import edu.uiowa.alloy2smt.Utils;
import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.printers.SmtLibPrettyPrinter;
import edu.uiowa.smt.smtAst.SmtProgram;
import edu.uiowa.smt.smtAst.SmtSettings;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import java.util.HashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertTrue;

public class SmtSettingsTests
{
    @Test
    void settings()
    {
        SmtSettings smtSettings = SmtSettings.getInstance();
        smtSettings.putSolverOption("tlimit", "5000");
        smtSettings.putSolverOption("produce-unsat-cores", "true");

        SmtLibPrettyPrinter printer = new SmtLibPrettyPrinter(smtSettings);
        printer.visit(smtSettings);
        String script = printer.getSmtLib();
        assertTrue(script.contains("(set-option :tlimit 5000)\n"));
        assertTrue(script.contains("(set-option :produce-unsat-cores true)\n"));
    }
}

