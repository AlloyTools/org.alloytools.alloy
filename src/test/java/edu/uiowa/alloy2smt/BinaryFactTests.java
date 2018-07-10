package edu.uiowa.alloy2smt;

import edu.uiowa.alloy2smt.translators.TranslatorUtils;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.function.Executable;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;


class BinaryFactTests
{

    private final String prefix =
            "(set-logic ALL)\n" +
            "(set-option :produce-models true)\n" +
            "(set-option :finite-model-find true)\n" +
            "(declare-sort Atom 0)\n";

    @BeforeEach
    public void beforeEach()
    {
        TranslatorUtils.reset();
    }

    @Test
    public void cardinality1()
    {
        String input =
                "sig A {}\n" +
                "fact f {#A = 2}";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "(declare-fun _S1 () (Set (Tuple Atom )))\n" +
                "(declare-const _a1 Atom)\n" +
                "(declare-const _a2 Atom)\n" +
                "(assert (distinct (mkTuple _a1 ) (mkTuple _a2 ) ))\n" +
                "(assert (= _S1 (insert (mkTuple _a1 ) (singleton (mkTuple _a2 )) )))\n" +
                "; f\n" +
                "(assert (= this_A _S1))\n";
        assertEquals(expected, actual);
    }


    @Test
    public void cardinality2()
    {
        String input =
                "sig A {}\n" +
                        "fact f {2 = #A}";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                        "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                        "(declare-fun _S1 () (Set (Tuple Atom )))\n" +
                        "(declare-const _a1 Atom)\n" +
                        "(declare-const _a2 Atom)\n" +
                        "(assert (distinct (mkTuple _a1 ) (mkTuple _a2 ) ))\n" +
                        "(assert (= _S1 (insert (mkTuple _a1 ) (singleton (mkTuple _a2 )) )))\n" +
                        "; f\n" +
                        "(assert (= this_A _S1))\n";
        assertEquals(expected, actual);
    }


    @Test
    public void cardinality3()
    {
        String input =
                "sig A {}\n" +
                "sig B {r: set A}\n" +
                "fact f {#B.r = 2 }";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "(declare-fun this_B () (Set (Tuple Atom )))\n" +
                "(declare-fun this_B_r () (Set (Tuple Atom Atom )))\n" +
                "(declare-fun _S1 () (Set (Tuple Atom )))\n" +
                "(declare-const _a1 Atom)\n" +
                "(declare-const _a2 Atom)\n" +
                "(assert (subset this_B_r (product this_B this_A)))\n" +
                "(assert (distinct (mkTuple _a1 ) (mkTuple _a2 ) ))\n" +
                "(assert (= _S1 (insert (mkTuple _a1 ) (singleton (mkTuple _a2 )) )))\n" +
                "; f\n" +
                "(assert (= (join this_B this_B_r) _S1))\n";
        assertEquals(expected, actual);
    }

    @Test
    public void cardinality4()
    {
        String input =
                "sig A {}\n" +
                "fact f {#A != 2}";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "(declare-fun _S1 () (Set (Tuple Atom )))\n" +
                "(declare-const _a1 Atom)\n" +
                "(declare-const _a2 Atom)\n" +
                "(assert (distinct (mkTuple _a1 ) (mkTuple _a2 ) ))\n" +
                "(assert (= _S1 (insert (mkTuple _a1 ) (singleton (mkTuple _a2 )) )))\n" +
                "; f\n" +
                "(assert (not (= this_A _S1)))\n";
        assertEquals(expected, actual);
    }

    @Test
    public void cardinality5()
    {
        String input =
                "sig A {}\n" +
                    "fact f {#A <= 2}";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "(declare-fun _S1 () (Set (Tuple Atom )))\n" +
                "(declare-const _a1 Atom)\n" +
                "(declare-const _a2 Atom)\n" +
                "(assert (distinct (mkTuple _a1 ) (mkTuple _a2 ) ))\n" +
                "(assert (= _S1 (insert (mkTuple _a1 ) (singleton (mkTuple _a2 )) )))\n" +
                "; f\n" +
                "(assert (subset this_A _S1))\n";
        assertEquals(expected, actual);
    }

    @Test
    public void cardinality6()
    {
        String input =
                "sig A {}\n" +
                "fact f {#A > 2}";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                        "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                        "(declare-fun _S1 () (Set (Tuple Atom )))\n" +
                        "(declare-const _a1 Atom)\n" +
                        "(declare-const _a2 Atom)\n" +
                        "(assert (distinct (mkTuple _a1 ) (mkTuple _a2 ) ))\n" +
                        "(assert (= _S1 (insert (mkTuple _a1 ) (singleton (mkTuple _a2 )) )))\n" +
                        "; f\n" +
                        "(assert (and (subset _S1 this_A) (not (= this_A _S1))))\n";
        assertEquals(expected, actual);
    }

    @Test
    public void cardinality7()
    {
        String input =
                "sig A {}\n" +
                "fact f {#A < 2}";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "(declare-fun _S1 () (Set (Tuple Atom )))\n" +
                "(declare-const _a1 Atom)\n" +
                "(declare-const _a2 Atom)\n" +
                "(assert (distinct (mkTuple _a1 ) (mkTuple _a2 ) ))\n" +
                "(assert (= _S1 (insert (mkTuple _a1 ) (singleton (mkTuple _a2 )) )))\n" +
                "; f\n" +
                "(assert (and (subset this_A _S1) (not (= this_A _S1))))\n";
        assertEquals(expected, actual);
    }

    @Test
    public void cardinality8()
    {
        String input =
                "sig A {}\n" +
                "fact f {#A >= 2}";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                        "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                        "(declare-fun _S1 () (Set (Tuple Atom )))\n" +
                        "(declare-const _a1 Atom)\n" +
                        "(declare-const _a2 Atom)\n" +
                        "(assert (distinct (mkTuple _a1 ) (mkTuple _a2 ) ))\n" +
                        "(assert (= _S1 (insert (mkTuple _a1 ) (singleton (mkTuple _a2 )) )))\n" +
                        "; f\n" +
                        "(assert (subset _S1 this_A))\n";
        assertEquals(expected, actual);
    }

    @Test
    public void cardinalityUnsupported()
    {
        String input =
                "sig A {}\n" +
                "fact f {#A > #A}";


        Executable executable = () -> Utils.translateFromString(input);

        assertThrows(UnsupportedOperationException.class, executable);
    }

    @Test
    public void lt()
    {
        String input =
                "sig A {}\n" +
                "fact f {2 < 3}";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "; f\n" +
                "(assert (< 2 3))\n";
        assertEquals(expected, actual);
    }

    @Test
    public void lte()
    {
        String input =
                "sig A {}\n" +
                "fact f {2 <= 3}";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "; f\n" +
                "(assert (<= 2 3))\n";
        assertEquals(expected, actual);
    }

    @Test
    public void gt()
    {
        String input =
                "sig A {}\n" +
                "fact f {2 > 3}";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "; f\n" +
                "(assert (> 2 3))\n";
        assertEquals(expected, actual);
    }

    @Test
    public void gte()
    {
        String input =
                "sig A {}\n" +
                "fact f {2 >= 3}";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "; f\n" +
                "(assert (>= 2 3))\n";
        assertEquals(expected, actual);
    }

    @Test
    public void eq()
    {
        String input =
                "sig A {}\n" +
                "fact f {2 = 3}";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "; f\n" +
                "(assert (= 2 3))\n";
        assertEquals(expected, actual);
    }

    @Test
    public void notEq()
    {
        String input =
                "sig A {}\n" +
                "fact f {2 != 3}";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                        "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                        "; f\n" +
                        "(assert (not (= 2 3)))\n";
        assertEquals(expected, actual);
    }
}