package edu.uiowa.alloy2smt.translators;

import edu.uiowa.alloy2smt.Utils;
import edu.uiowa.alloy2smt.smtAst.Assertion;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

class CommandTranslationTests
{

    @BeforeEach
    void setUp()
    {
        TranslatorUtils.reset();
    }

    @Test
    void runCommand1()
    {
        String alloy =
                "sig A {}\n" +
                "run command1 {#A = 1 or #A = 2} for 10";
        Translation translation = Utils.translate(alloy);

        Assertions.assertFalse(translation.getSmtScript().contains("(check-sat)"));
        Assertions.assertFalse(translation.getSmtScript().contains("(get-model)"));

        String command = translation.translateCommand(0);

        Assertions.assertEquals("; command1\n" +
                "(assert (or (exists ((_a3 Atom)) (and (= this_A (singleton (mkTuple _a3))) (distinct _a3))) (exists ((_a4 Atom)(_a5 Atom)) (and (= this_A (insert (mkTuple _a5) (singleton (mkTuple _a4)))) (distinct _a4 _a5)))))\n", command);
    }
}