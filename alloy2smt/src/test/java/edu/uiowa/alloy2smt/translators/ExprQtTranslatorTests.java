package edu.uiowa.alloy2smt.translators;

import edu.uiowa.alloy2smt.utils.AlloyUtils;
import edu.uiowa.alloy2smt.utils.CommandResult;
import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.smtAst.FunctionDefinition;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class ExprQtTranslatorTests
{

    @Test
    void allIntQuantifier() throws Exception
    {
        String alloy = "sig A in Int {}\n" +
                        "fact f1{#A = 2}\n" +
                        "fact f1{all x : A | x > 5}";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertEquals("sat", commandResults.get(0).satResult);
        FunctionDefinition a = AlloyUtils.getFunctionDefinition(commandResults.get(0), "this/A");
        Set<Integer> aAtoms = TranslatorUtils.getIntSet(a);
        assertEquals(2, aAtoms.size());
        assertTrue(new ArrayList<>(aAtoms).get(0) > 5);
        assertTrue(new ArrayList<>(aAtoms).get(1) > 5);
    }

    @Test
    void allQuantifier() throws Exception
    {
        String alloy = "abstract sig A {}\n" +
                "one sig A0, A1 extends A {}\n" +
                "fact f1{all x : A | x in A0}";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertEquals("unsat", commandResults.get(0).satResult);
    }

    @Test
    void someQuantifier() throws Exception
    {
        String alloy = "abstract sig A {}\n" +
                "one sig A0, A1 extends A {}\n" +
                "fact f1{some x : A | x in A}";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertEquals("sat", commandResults.get(0).satResult);
    }

    @Test
    void allQuantifierMultipleDeclarations() throws Exception
    {
        String alloy = "abstract sig A {}\n" +
                "one sig A0, A1 extends A {}\n" +
                "fact f1{all x : A, y : A - x | A = x + y}";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertEquals("sat", commandResults.get(0).satResult);

        FunctionDefinition a = AlloyUtils.getFunctionDefinition(commandResults.get(0), "this/A");
        Set<String> aAtoms = TranslatorUtils.getAtomSet(a);
        assertEquals(2, aAtoms.size());
    }

    @Test
    void someQuantifierMultipleDeclarations() throws Exception
    {
        String alloy = "abstract sig A {}\n" +
                "one sig A0, A1 extends A {}\n" +
                "fact f1{some x : A, y : A - x | A = x + y}";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertEquals("sat", commandResults.get(0).satResult);

        FunctionDefinition a = AlloyUtils.getFunctionDefinition(commandResults.get(0), "this/A");
        Set<String> aAtoms = TranslatorUtils.getAtomSet(a);
        assertEquals(2, aAtoms.size());
    }


    @Test
    void oneQuantifier() throws Exception
    {
        String alloy = "sig A {} fact {one x : A | x != none}";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertEquals("sat", commandResults.get(0).satResult);
        FunctionDefinition a = AlloyUtils.getFunctionDefinition(commandResults.get(0), "this/A");
        Set<String> aAtoms = TranslatorUtils.getAtomSet(a);
        assertEquals(1, aAtoms.size());
    }

    @Test
    void oneQuantifierMultipleDeclarations() throws Exception
    {
        String alloy =
                "sig A {}\n" +
                "sig A0, A1 in A {} \n" +
                "fact {one x, y: A | x = A0 and y = A1 and x != y}";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertEquals("sat", commandResults.get(0).satResult);
        FunctionDefinition a = AlloyUtils.getFunctionDefinition(commandResults.get(0), "this/A");
        Set<String> aAtoms = TranslatorUtils.getAtomSet(a);
        assertEquals(2, aAtoms.size());
    }

    @Test
    void loneQuantifierMultipleDeclarations() throws Exception
    {
        String alloy =
                "abstract sig A {}\n" +
                "one sig A0, A1 extends A {} \n" +
                "fact f1{lone x, y: A | x = A0 and y = A0 and x != y}";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertEquals("sat", commandResults.get(0).satResult);
        FunctionDefinition a = AlloyUtils.getFunctionDefinition(commandResults.get(0), "this/A");
        Set<String> aAtoms = TranslatorUtils.getAtomSet(a);
        assertEquals(2, aAtoms.size());
    }

    @Test
    void secondOrderSomeSet() throws Exception
    {
        String alloy =
                "sig A {}\n" +
                "fact f{some x: set A | x = A and x = none}";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertEquals("sat", commandResults.get(0).satResult);
        FunctionDefinition a = AlloyUtils.getFunctionDefinition(commandResults.get(0), "this/A");
        Set<String> aAtoms = TranslatorUtils.getAtomSet(a);
        assertEquals(0, aAtoms.size());
    }

    @Test
    void secondOrderSomeSome1() throws Exception
    {
        String alloy =
                "sig A {}\n" +
                "fact f{some x: some A | x = none}";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertEquals("unsat", commandResults.get(0).satResult);
    }

    @Test
    void secondOrderAllSome() throws Exception
    {
        String alloy =
                "abstract sig A {}\n" +
                "sig A0, A1 extends A {}\n" +
                "fact f1 {#A0 = 2 and #A1 = 1}\n" +
                "fact f{not all x: some A0, y: some A1 |  x + y != A}";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertEquals("sat", commandResults.get(0).satResult);
    }

    @Test
    void secondOrderOneLone() throws Exception
    {
        String alloy =
                "abstract sig A {}\n" +
                "sig A0, A1 extends A {}\n" +
                "fact f1 {#A0 = 2 and #A1 = 1}\n" +
                "fact f{not one x: lone A0, y: lone A1 |  x + y = A}";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertEquals("unsat", commandResults.get(0).satResult);
    }

    @Test
    void comprehension() throws Exception
    {
        String alloy =
                "sig A {}\n" +
                "sig A0, A1 in A {}\n" +
                "fact f1 {#A0 = 2 and #A1 = 1}\n" +
                "fact f{ A0= {x: A | x not in A1}}";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertEquals("sat", commandResults.get(0).satResult);
        FunctionDefinition a = AlloyUtils.getFunctionDefinition(commandResults.get(0), "this/A");
        Set<String> aAtoms = TranslatorUtils.getAtomSet(a);
        assertEquals(3, aAtoms.size());

        FunctionDefinition a0 = AlloyUtils.getFunctionDefinition(commandResults.get(0), "this/A0");
        Set<String> a0Atoms = TranslatorUtils.getAtomSet(a0);
        assertEquals(2, a0Atoms.size());
    }


    @Test
    void disjointSingletons() throws Exception
    {
        String alloy =
            "sig A {}\n" +
            "assert distinct {all disj x, y : A | x != y}\n" +
            "check distinct";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertEquals("unsat", commandResults.get(0).satResult);
    }

    @Test
    void disjointSets1() throws Exception
    {
        String alloy =
                "sig A {}\n" +
                "assert distinct {all disj x, y : set A | x != y}\n" +
                 "check distinct";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertEquals("sat", commandResults.get(0).satResult);
        FunctionDefinition a = AlloyUtils.getFunctionDefinition(commandResults.get(0), "this/A");
        Set<String> aAtoms = TranslatorUtils.getAtomSet(a);
        assertEquals(0, aAtoms.size());
    }

    @Test
    void disjointSets2() throws Exception
    {
        String alloy =
                "sig A {}\n" +
                "assert distinct {all disj x, y : set A | (some x and some y) => x != y}\n" +
                "check distinct";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertEquals("unsat", commandResults.get(0).satResult);
    }

    @Test
    void functionComprehension() throws Exception
    {
        String alloy =
                "sig A {}\n" +
                "sig A0, A1 in A {}\n" +
                "fun complement1[x: A]: A {let x' = {y : A | not (y in x)} | x'}\n" +
                "fun complement2[x: A]: A {A - x}\n" +
                "fact{\n" +
                "#A0 = 2 and #A1 = 2 and\n" +
                "complement1[A0] = A1 and\n" +
                "complement1[A1] = A0 and\n" +
                "A0 = A1\n" +
                "}";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertEquals("unsat", commandResults.get(0).satResult);
    }
}
