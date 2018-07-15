package edu.uiowa.alloy2smt;

import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.function.Executable;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;


class BinaryFactTests extends TestBase
{
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
                "(declare-const _a1 (Tuple Atom ))\n" +
                "(declare-const _a2 (Tuple Atom ))\n" +
                "(assert (distinct _a1 _a2 ))\n" +
                "(assert (= _S1 (insert _a1 (singleton _a2) )))\n" +
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
                        "(declare-const _a1 (Tuple Atom ))\n" +
                        "(declare-const _a2 (Tuple Atom ))\n" +
                        "(assert (distinct _a1 _a2 ))\n" +
                        "(assert (= _S1 (insert _a1 (singleton _a2) )))\n" +
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
                "(declare-const _a1 (Tuple Atom ))\n" +
                "(declare-const _a2 (Tuple Atom ))\n" +
                "(assert (subset this_B_r (product this_B this_A)))\n" +
                "(assert (distinct _a1 _a2 ))\n" +
                "(assert (= _S1 (insert _a1 (singleton _a2) )))\n" +
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
                "(declare-const _a1 (Tuple Atom ))\n" +
                "(declare-const _a2 (Tuple Atom ))\n" +
                "(assert (distinct _a1 _a2 ))\n" +
                "(assert (= _S1 (insert _a1 (singleton _a2) )))\n" +
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
                "(declare-const _a1 (Tuple Atom ))\n" +
                "(declare-const _a2 (Tuple Atom ))\n" +
                "(assert (distinct _a1 _a2 ))\n" +
                "(assert (= _S1 (insert _a1 (singleton _a2) )))\n" +
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
                "(declare-const _a1 (Tuple Atom ))\n" +
                "(declare-const _a2 (Tuple Atom ))\n" +
                "(assert (distinct _a1 _a2 ))\n" +
                "(assert (= _S1 (insert _a1 (singleton _a2) )))\n" +
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
                "(declare-const _a1 (Tuple Atom ))\n" +
                "(declare-const _a2 (Tuple Atom ))\n" +
                "(assert (distinct _a1 _a2 ))\n" +
                "(assert (= _S1 (insert _a1 (singleton _a2) )))\n" +
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
                "(declare-const _a1 (Tuple Atom ))\n" +
                "(declare-const _a2 (Tuple Atom ))\n" +
                "(assert (distinct _a1 _a2 ))\n" +
                "(assert (= _S1 (insert _a1 (singleton _a2) )))\n" +
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


    @Test
    public void union()
    {
        String input =
                "sig A {}\n" +
                "sig B {}\n" +
                "fact f { #(A + B) = 3 }";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "(declare-fun this_B () (Set (Tuple Atom )))\n" +
                "(declare-fun _S1 () (Set (Tuple Atom )))\n" +
                "(declare-const _a1 (Tuple Atom ))\n" +
                "(declare-const _a2 (Tuple Atom ))\n" +
                "(declare-const _a3 (Tuple Atom ))\n" +
                "(assert (distinct _a1 _a2 _a3 ))\n" +
                "(assert (= _S1 (insert _a1 _a2 (singleton _a3) )))\n" +
                "; f\n" +
                "(assert (= (union this_A this_B) _S1))\n";
        assertEquals(expected, actual);
    }

    @Test
    public void intersection()
    {
        String input =
            "sig A {}\n" +
            "sig B, C in A {}\n" +
            "fact f { #(B & C) = 3 }";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "(declare-fun this_B () (Set (Tuple Atom )))\n" +
                "(declare-fun this_C () (Set (Tuple Atom )))\n" +
                "(declare-fun _S1 () (Set (Tuple Atom )))\n" +
                "(declare-const _a1 (Tuple Atom ))\n" +
                "(declare-const _a2 (Tuple Atom ))\n" +
                "(declare-const _a3 (Tuple Atom ))\n" +
                "(assert (subset this_B this_A))\n" +
                "(assert (subset this_C this_A))\n" +
                "(assert (distinct _a1 _a2 _a3 ))\n" +
                "(assert (= _S1 (insert _a1 _a2 (singleton _a3) )))\n" +
                "; f\n" +
                "(assert (= (intersection this_B this_C) _S1))\n";
        assertEquals(expected, actual);
    }

    @Test
    public void difference()
    {
        String input =
                "sig A {}\n" +
                "sig B, C in A {}\n" +
                "fact f { #(B - C) = 2 }";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "(declare-fun this_B () (Set (Tuple Atom )))\n" +
                "(declare-fun this_C () (Set (Tuple Atom )))\n" +
                "(declare-fun _S1 () (Set (Tuple Atom )))\n" +
                "(declare-const _a1 (Tuple Atom ))\n" +
                "(declare-const _a2 (Tuple Atom ))\n" +
                "(assert (subset this_B this_A))\n" +
                "(assert (subset this_C this_A))\n" +
                "(assert (distinct _a1 _a2 ))\n" +
                "(assert (= _S1 (insert _a1 (singleton _a2) )))\n" +
                "; f\n" +
                "(assert (= (setminus this_B this_C) _S1))\n";
        assertEquals(expected, actual);
    }

    @Test
    public void equality()
    {
        String input =
                "sig A {}\n" +
                "sig B, C in A {}\n" +
                "fact f { B = C }";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "(declare-fun this_B () (Set (Tuple Atom )))\n" +
                "(declare-fun this_C () (Set (Tuple Atom )))\n" +
                "(assert (subset this_B this_A))\n" +
                "(assert (subset this_C this_A))\n" +
                "; f\n" +
                "(assert (= this_B this_C))\n";
        assertEquals(expected, actual);
    }

    @Test
    public void in()
    {
        String input =
                "sig A {}\n" +
                "sig B, C in A {}\n" +
                "fact f { B in C }";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "(declare-fun this_B () (Set (Tuple Atom )))\n" +
                "(declare-fun this_C () (Set (Tuple Atom )))\n" +
                "(assert (subset this_B this_A))\n" +
                "(assert (subset this_C this_A))\n" +
                "; f\n" +
                "(assert (subset this_B this_C))\n";
        assertEquals(expected, actual);
    }

    @Test
    public void notIn()
    {
        String input =
                "sig A {}\n" +
                "sig B, C in A {}\n" +
                "fact f { B !in C }";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "(declare-fun this_B () (Set (Tuple Atom )))\n" +
                "(declare-fun this_C () (Set (Tuple Atom )))\n" +
                "(assert (subset this_B this_A))\n" +
                "(assert (subset this_C this_A))\n" +
                "; f\n" +
                "(assert (not (subset this_B this_C)))\n";
        assertEquals(expected, actual);
    }

    @Test
    public void domainRestriction1()
    {
        String input =
                "sig A {}\n" +
                "sig B {r: set A}\n" +
                "fact f {#(B <: r) = 2}";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "(declare-fun this_B () (Set (Tuple Atom )))\n" +
                "(declare-fun this_B_r () (Set (Tuple Atom Atom )))\n" +
                "(declare-fun _S1 () (Set (Tuple Atom Atom )))\n" +
                "(declare-const _a1 (Tuple Atom Atom ))\n" +
                "(declare-const _a2 (Tuple Atom Atom ))\n" +
                "(assert (subset this_B_r (product this_B this_A)))\n" +
                "(assert (distinct _a1 _a2 ))\n" +
                "(assert (= _S1 (insert _a1 (singleton _a2) )))\n" +
                "; f\n" +
                "(assert (= this_B_r _S1))\n";
        assertEquals(expected, actual);
    }

    @Test
    public void domainRestriction2()
    {
        String input =
                "sig A {}\n" +
                "sig B {r: set A}\n" +
                "sig B1, B2 in B {}\n" +
                "fact f {#(B1 <: r) = 2}";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "(declare-fun this_B () (Set (Tuple Atom )))\n" +
                "(declare-fun this_B_r () (Set (Tuple Atom Atom )))\n" +
                "(declare-fun this_B1 () (Set (Tuple Atom )))\n" +
                "(declare-fun this_B2 () (Set (Tuple Atom )))\n" +
                "(declare-fun _S1 () (Set (Tuple Atom Atom )))\n" +
                "(declare-const _a1 (Tuple Atom Atom ))\n" +
                "(declare-const _a2 (Tuple Atom Atom ))\n" +
                "(assert (subset this_B_r (product this_B this_A)))\n" +
                "(assert (subset this_B1 this_B))\n" +
                "(assert (subset this_B2 this_B))\n" +
                "(assert (distinct _a1 _a2 ))\n" +
                "(assert (= _S1 (insert _a1 (singleton _a2) )))\n" +
                "; f\n" +
                "(assert (= (intersection (product this_B1 (as univset (Set (Tuple Atom )))) this_B_r) _S1))\n";
        assertEquals(expected, actual);
    }

    @Disabled
    @Test
    public void domainRestriction3()
    {
        String input =
                "sig A,B {}\n" +
                "sig C {r: A set -> set B}\n" +
                "sig C1, C2 in C {}\n" +
                "fact f {#(C1 <: r) = 2}";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                        "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                        "(declare-fun this_B () (Set (Tuple Atom )))\n" +
                        "(declare-fun this_B_r () (Set (Tuple Atom Atom )))\n" +
                        "(declare-fun this_B1 () (Set (Tuple Atom )))\n" +
                        "(declare-fun this_B2 () (Set (Tuple Atom )))\n" +
                        "(declare-fun _S1 () (Set (Tuple Atom Atom )))\n" +
                        "(declare-const _a1 (Tuple Atom Atom ))\n" +
                        "(declare-const _a2 (Tuple Atom Atom ))\n" +
                        "(assert (subset this_B_r (product this_B this_A)))\n" +
                        "(assert (subset this_B1 this_B))\n" +
                        "(assert (subset this_B2 this_B))\n" +
                        "(assert (distinct _a1 _a2 ))\n" +
                        "(assert (= _S1 (insert _a1 (singleton _a2) )))\n" +
                        "; f\n" +
                        "(assert (= (intersection (product this_B1 (as univset (Set (Tuple Atom )))) this_B_r) _S1))\n";
        assertEquals(expected, actual);
    }


    @Test
    public void rangeRestriction1()
    {
        String input =
                "sig A {}\n" +
                "sig B {r: set A}\n" +
                "fact f {#(r :> A) = 2}";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "(declare-fun this_B () (Set (Tuple Atom )))\n" +
                "(declare-fun this_B_r () (Set (Tuple Atom Atom )))\n" +
                "(declare-fun _S1 () (Set (Tuple Atom Atom )))\n" +
                "(declare-const _a1 (Tuple Atom Atom ))\n" +
                "(declare-const _a2 (Tuple Atom Atom ))\n" +
                "(assert (subset this_B_r (product this_B this_A)))\n" +
                "(assert (distinct _a1 _a2 ))\n" +
                "(assert (= _S1 (insert _a1 (singleton _a2) )))\n" +
                "; f\n" +
                "(assert (= (intersection this_B_r (product this_A (as univset (Set (Tuple Atom ))))) _S1))\n";
        assertEquals(expected, actual);
    }

    @Test
    public void rangeRestriction2()
    {
        String input =
                "sig A {}\n" +
                "sig B {r: set A}\n" +
                "sig A1, A2 in A {}\n" +
                "fact f {#(r :> A1) = 2}";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "(declare-fun this_B () (Set (Tuple Atom )))\n" +
                "(declare-fun this_B_r () (Set (Tuple Atom Atom )))\n" +
                "(declare-fun this_A1 () (Set (Tuple Atom )))\n" +
                "(declare-fun this_A2 () (Set (Tuple Atom )))\n" +
                "(declare-fun _S1 () (Set (Tuple Atom Atom )))\n" +
                "(declare-const _a1 (Tuple Atom Atom ))\n" +
                "(declare-const _a2 (Tuple Atom Atom ))\n" +
                "(assert (subset this_B_r (product this_B this_A)))\n" +
                "(assert (subset this_A1 this_A))\n" +
                "(assert (subset this_A2 this_A))\n" +
                "(assert (distinct _a1 _a2 ))\n" +
                "(assert (= _S1 (insert _a1 (singleton _a2) )))\n" +
                "; f\n" +
                "(assert (= (intersection this_B_r (product this_A1 (as univset (Set (Tuple Atom ))))) _S1))\n";
        assertEquals(expected, actual);
    }

}