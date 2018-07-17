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

    protected String getSuffix(int lastIndex)
    {

        String suffix = MessageFormat.format(
                "(assert (forall ((_x{0} Atom)(_x{1} Atom)) " +
                        "(=> " +
                            "(and " +
                                "(member (mkTuple _x{0} ) (as univset (Set (Tuple Atom )))) " +
                                "(member (mkTuple _x{1} ) (as univset (Set (Tuple Atom ))))) " +
                            "(= " +
                                "(member (mkTuple _x{0} _x{1} ) identity) " +
                                "(= _x{0} _x{1})))))\n", lastIndex + 1, lastIndex + 2);
        return suffix;
    }
}
