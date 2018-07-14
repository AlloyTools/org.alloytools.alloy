package edu.uiowa.alloy2smt;

import edu.uiowa.alloy2smt.translators.TranslatorUtils;
import org.junit.jupiter.api.BeforeEach;

public class TestBase
{
    protected final String prefix =
            "(set-logic ALL)\n" +
            "(set-option :produce-models true)\n" +
            "(set-option :finite-model-find true)\n" +
            "(set-option :sets-ext true)\n" +
            "(declare-sort Atom 0)\n";

    @BeforeEach
    protected void beforeEach()
    {
        TranslatorUtils.reset();
    }

}
