package edu.uiowa.alloy2smt.translators;

import edu.uiowa.alloy2smt.Utils;
import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.printers.SmtLibPrettyPrinter;
import edu.uiowa.smt.smtAst.SmtProgram;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import java.util.HashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertTrue;

public class SolverOptionsTests
{
    @Test
    void options()
    {
        Map<String, String> options = new HashMap<>();
        options.put("tlimit", "30000");
        options.put("produce-unsat-cores", "true");

        SmtLibPrettyPrinter printer = new SmtLibPrettyPrinter(options);
        SmtProgram emptyProgram = new SmtProgram();
        printer.visit(emptyProgram);
        String script = printer.getSmtLib();
        assertTrue(script.contains("(set-option :tlimit 30000)\n"));
        assertTrue(script.contains("(set-option :produce-unsat-cores true)\n"));
    }
}

