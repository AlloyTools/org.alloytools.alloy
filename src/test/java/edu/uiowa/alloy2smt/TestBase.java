package edu.uiowa.alloy2smt;

import edu.uiowa.alloy2smt.translators.TranslatorUtils;
import org.junit.jupiter.api.BeforeEach;

import java.text.MessageFormat;

public class TestBase
{
    protected final String prefix =
            "(set-logic ALL)\n" +
            "(set-option :produce-models true)\n" +
            "(set-option :finite-model-find true)\n" +
            "(set-option :sets-ext true)\n" +
            "(declare-sort Atom 0)\n" +
            "(declare-fun identity () (Set (Tuple Atom Atom )))\n";

    @BeforeEach
    protected void beforeEach()
    {
        TranslatorUtils.reset();
    }

    protected String getSuffix()
    {

        String suffix =
                "(assert (forall ((_x1 Atom)(_x2 Atom)) " +
                        "(=> " +
                            "(and " +
                                "(member (mkTuple _x1 ) (as univset (Set (Tuple Atom )))) " +
                                "(member (mkTuple _x2 ) (as univset (Set (Tuple Atom ))))) " +
                            "(= " +
                                "(member (mkTuple _x1 _x2 ) identity) " +
                                "(= _x1 _x2)))))\n";
        return suffix;
    }
}
