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

    @Test
    public void noFactRelation()
    {
        String input =
                "sig A {}\n" +
                "sig B {r: A}\n" +
                "fact f {no B.r }";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "(declare-fun this_B () (Set (Tuple Atom )))\n" +
                "(declare-fun this_B_r () (Set (Tuple Atom Atom )))\n" +
                "(assert (subset this_B_r (product this_B this_A)))\n" +
                "(assert (forall ((_x1 Atom)) (=> (member (mkTuple _x1 ) this_B) (exists ((_x2 Atom)) (and (member (mkTuple _x2 ) this_A) (and (member (mkTuple _x1 _x2 ) this_B_r) (forall ((_x3 Atom)) (=> (and (member (mkTuple _x3 ) this_A) (not (= _x3 _x2))) (not (member (mkTuple _x1 _x3 ) this_B_r))))))))))\n" +
                "; f\n" +
                "(assert (forall ((_x4 Atom)) (not (member (mkTuple _x4 ) (join this_B this_B_r)))))\n";
        assertEquals(expected, actual);
    }
}