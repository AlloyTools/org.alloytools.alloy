package edu.uiowa.alloy2smt.translators;

import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.smtAst.FunctionDefinition;
import edu.uiowa.alloy2smt.utils.CommandResult;
import edu.uiowa.alloy2smt.utils.AlloyUtils;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

class FieldTranslatorTests
{
    @Test
    void oneMultiplicity() throws Exception
    {
        String alloy = "sig a {f: a}";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        FunctionDefinition a = AlloyUtils.getFunctionDefinition(commandResults.get(0), "this_a");
    }

    @Test
    void oneMultiplicityInt() throws Exception
    {
        String alloy = "sig a in Int {f: a}";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        FunctionDefinition a = AlloyUtils.getFunctionDefinition(commandResults.get(0), "this_a");
    }

    @Test
    void arity1() throws Exception
    {
        String alloy =
                "abstract sig b, c, d {}\n" +
                "abstract sig a {r: b -> c -> d}\n" +
                "\n" +
                "one sig a0, a1, a2 extends a {}\n" +
                "one sig b0, b1, b2 extends b {}\n" +
                "one sig c0, c1, c2 extends c {}\n" +
                "one sig d0, d1, d2 extends d {}\n" +
                "fact {r = a0 -> b0 -> c0 -> d0}";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertEquals("sat", commandResults.get(0).satResult);
    }

    @Test
    void arity2() throws Exception
    {
        String alloy =
                "abstract sig b, c, d {}\n" +
                        "abstract sig a {r: b -> lone c -> d}\n" +
                        "\n" +
                        "one sig a0, a1, a2 extends a {}\n" +
                        "one sig b0, b1, b2 extends b {}\n" +
                        "one sig c0, c1, c2 extends c {}\n" +
                        "one sig d0, d1, d2 extends d {}\n" +
                        "fact {no r}";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertEquals("sat", commandResults.get(0).satResult);
    }

    @Test
    void arity3() throws Exception
    {
        String alloy =
            "sig s{r: s ->s -> s}\n" +
            "fact {all x, y: s | x -> y in s -> s implies y.(x.r) in s one -> one s }";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertEquals("sat", commandResults.get(0).satResult);
    }

    @Test
    void fieldUnaryWithUnion() throws Exception
    {
        String alloy =
                "sig B {}\n" +
                "sig A {r: set A + B}\n" +
                "fact {#r = 2 and A.r = A + B and #B = 1}";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertEquals("sat", commandResults.get(0).satResult);

        FunctionDefinition r = AlloyUtils.getFunctionDefinition(commandResults.get(0), "this_A_r");
        Set<List<String>> rElements = TranslatorUtils.getRelation(r);
        assertEquals(2, rElements.size());

        FunctionDefinition a = AlloyUtils.getFunctionDefinition(commandResults.get(0), "this_A");
        Set<String> aAtoms = TranslatorUtils.getAtomSet(a);
        assertEquals(1, aAtoms.size());

        FunctionDefinition b = AlloyUtils.getFunctionDefinition(commandResults.get(0), "this_B");
        Set<List<String>> bElements = TranslatorUtils.getRelation(b);
        assertEquals(1, bElements.size());
    }

    @Test
    void fieldBinaryWithUnion() throws Exception
    {
        String alloy =
                "sig B {}\n" +
                "sig A {r: A -> (A + B)}\n" +
                "fact {A.(A.r) = (A + B) and A != none and B != none}";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertEquals("sat", commandResults.get(0).satResult);
    }

    @Test
    void fieldDependsOnAnotherField() throws Exception
    {
        String alloy = "sig A {r: set A, s: r->some A} fact {(A.r).(A.s) != none}";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertEquals("sat", commandResults.get(0).satResult);
    }

    @Test
    void fieldDependsOnAnotherFields() throws Exception
    {
        String alloy = "sig A {r: set A, s: r->some A, t: r -> s} " +
                "fact {#t = 2}";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertEquals("sat", commandResults.get(0).satResult);
        FunctionDefinition t = AlloyUtils.getFunctionDefinition(commandResults.get(0), "this_A_t");
        Set<List<String>> tElements = TranslatorUtils.getRelation(t);
        assertEquals(2, tElements.size());
        for (List<String> element: tElements)
        {
            assertEquals(4, element.size());
        }
    }
}




