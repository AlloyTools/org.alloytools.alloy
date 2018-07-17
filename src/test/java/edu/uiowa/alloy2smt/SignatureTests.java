package edu.uiowa.alloy2smt;

import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;


class SignatureTests extends TestBase
{

    @Test
    public void simpleSignature()
    {

        String input = "sig A {}";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_A () (Set (Tuple Atom )))\n";
        assertEquals(expected + getSuffix(0), actual);
    }

    @Test
    public void extendedSignatures()
    {

        String input =
                "sig A {}\n" +
                "sig A1 extends A{}\n" +
                "sig A2 extends A{}" ;

        String actual = Utils.translateFromString(input);
        String expected =
                prefix  +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "(declare-fun this_A1 () (Set (Tuple Atom )))\n" +
                "(declare-fun this_A2 () (Set (Tuple Atom )))\n" +
                "(assert (subset this_A1 this_A))\n" +
                "(assert (subset this_A2 this_A))\n" +
                "(assert (= (intersection this_A1 this_A2) (as emptyset (Set (Tuple Atom )))))\n";
        assertEquals(expected + getSuffix(0), actual);
    }

    @Test
    public void abstractSignatures1()
    {

        String input =
                "abstract sig A {}\n" +
                "sig A1 extends A{}\n" +
                "sig A2 extends A{}" ;

        String actual = Utils.translateFromString(input);
        String expected =
                prefix  +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "(declare-fun this_A1 () (Set (Tuple Atom )))\n" +
                "(declare-fun this_A2 () (Set (Tuple Atom )))\n" +
                "(assert (subset this_A1 this_A))\n" +
                "(assert (subset this_A2 this_A))\n" +
                "(assert (= (intersection this_A1 this_A2) (as emptyset (Set (Tuple Atom )))))\n" +
                "(assert (= this_A (union this_A1 this_A2)))\n";
        assertEquals(expected + getSuffix(0), actual);
    }

    @Test
    public void abstractSignatures2()
    {

        String input =
                "abstract sig A {}\n" +
                "sig A1 extends A{}\n";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix  +
                        "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                        "(declare-fun this_A1 () (Set (Tuple Atom )))\n" +
                        "(assert (subset this_A1 this_A))\n" +
                        "(assert (= this_A this_A1))\n";
        assertEquals(expected + getSuffix(0), actual);
    }

    @Test
    public void abstractSignatures3()
    {

        String input = "abstract sig A {}";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix  +
                "(declare-fun this_A () (Set (Tuple Atom )))\n";
        assertEquals(expected + getSuffix(0), actual);
    }

    @Test
    public void subsetSignatures1()
    {

        String input =
                "sig A,B {}\n" +
                "sig A1 in A+B{}\n" +
                "sig A2 in A{}" ;

        String actual = Utils.translateFromString(input);
        String expected =
                prefix  +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "(declare-fun this_B () (Set (Tuple Atom )))\n" +
                "(declare-fun this_A1 () (Set (Tuple Atom )))\n" +
                "(declare-fun this_A2 () (Set (Tuple Atom )))\n" +
                "(assert (subset this_A1 (union this_A this_B)))\n" +
                "(assert (subset this_A2 this_A))\n";
        assertEquals(expected + getSuffix(0), actual);
    }

    @Test
    public void subsetSignatures2()
    {

        String input =
                "abstract sig A,B {}\n" +
                "sig A1 in A+B{}\n" +
                "sig A2 in A{}" ;

        String actual = Utils.translateFromString(input);
        String expected =
                prefix  +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "(declare-fun this_B () (Set (Tuple Atom )))\n" +
                "(declare-fun this_A1 () (Set (Tuple Atom )))\n" +
                "(declare-fun this_A2 () (Set (Tuple Atom )))\n" +
                "(assert (subset this_A1 (union this_A this_B)))\n" +
                "(assert (subset this_A2 this_A))\n";
        assertEquals(expected + getSuffix(0), actual);
    }

    @Test
    public void oneSignature()
    {

        String input = "one sig A {}";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "(declare-fun _S1 () (Set (Tuple Atom )))\n" +
                "(declare-const _a1 (Tuple Atom ))\n" +
                "(assert (= _S1 (singleton _a1)))\n" +
                "(assert (= this_A _S1))\n";
        assertEquals(expected + getSuffix(0), actual);
    }

    @Test
    public void loneSignature()
    {

        String input = "lone sig A {}";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "(declare-fun _S1 () (Set (Tuple Atom )))\n" +
                "(declare-const _a1 (Tuple Atom ))\n" +
                "(assert (= _S1 (singleton _a1)))\n" +
                "(assert (subset this_A _S1))\n";
        assertEquals(expected + getSuffix(0), actual);
    }

    @Test
    public void someSignature()
    {

        String input = "some sig A {}";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "(declare-fun _S1 () (Set (Tuple Atom )))\n" +
                "(declare-const _a1 (Tuple Atom ))\n" +
                "(assert (= _S1 (singleton _a1)))\n" +
                "(assert (subset _S1 this_A))\n";
        assertEquals(expected + getSuffix(0), actual);
    }

    @Disabled
    @Test
    public void unionOfTopLevelSignsIsTheUniverse()
    {
        assertTrue(false);
    }
}