package edu.uiowa.alloy2smt.translators;

import edu.uiowa.alloy2smt.Utils;
import edu.uiowa.smt.TranslatorUtils;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import java.util.HashMap;
import java.util.Map;

public class SolverOptionsTests
{
    @Test
    void options()
    {
        String alloy = "";
        Translation translation = Utils.translate(alloy);

        Map<String, String> options = new HashMap<>();
        options.put("tlimit", "30000");
        options.put("produce-unsat-cores", "true");

        String script = TranslatorUtils.translateOptions(options);
        Assertions.assertEquals(
        "(set-option :tlimit 30000)\n" +
                "(set-option :produce-unsat-cores true)\n",
                script);
    }
}

