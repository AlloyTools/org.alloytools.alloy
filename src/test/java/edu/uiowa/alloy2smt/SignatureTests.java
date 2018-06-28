package edu.uiowa.alloy2smt;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;


class SignatureTests
{

    private final String prefix =
            "(set-logic ALL)\n" +
            "(set-option :produce-models true)\n" +
            "(set-option :finite-model-find true)\n" +
            "(declare-sort Atom 0)\n";

    @BeforeEach
    public void beforeEach()
    {
        Utils.resetVariableNameIndex();
    }

    @Test
    public void simpleSignature()
    {

        String input = "sig A {}";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_A () (Set (Tuple Atom )))\n";
        assertEquals(expected, actual);
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
                "(assert (= (intersection this_A1 this_A2) (as emptyset (Set (Tuple Atom )))))\n" +
                "(assert (= (intersection this_A2 this_A1) (as emptyset (Set (Tuple Atom )))))\n";
        assertEquals(expected, actual);
    }

    @Test
    public void abstractSignatures()
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
                "(assert (= (intersection this_A2 this_A1) (as emptyset (Set (Tuple Atom )))))\n" +
                "(assert (= this_A (union this_A1 this_A2)))\n";
        assertEquals(expected, actual);
    }
}