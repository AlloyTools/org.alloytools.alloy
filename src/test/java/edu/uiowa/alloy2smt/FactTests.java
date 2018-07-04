package edu.uiowa.alloy2smt;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;


class FactTests
{

    private final String prefix =
            "(set-logic ALL)\n" +
            "(set-option :produce-models true)\n" +
            "(set-option :finite-model-find true)\n" +
            "(declare-sort Atom 0)\n";

    @BeforeEach
    public void beforeEach()
    {
        Utils.reset();
    }

    @Test
    public void simpleFact()
    {
        String input =
                "sig A {}\n" +
                "fact f {no A}";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "; f\n" +
                "(assert (forall ((_x1 Atom)) (not (member (mkTuple _x1 ) this_A))))\n";
        assertEquals(expected, actual);
    }
}