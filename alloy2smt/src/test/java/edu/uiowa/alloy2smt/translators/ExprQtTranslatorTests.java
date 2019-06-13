package edu.uiowa.alloy2smt.translators;

import edu.uiowa.alloy2smt.utils.AlloyUtils;
import edu.uiowa.alloy2smt.utils.CommandResult;
import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.smtAst.FunctionDefinition;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

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
        FunctionDefinition a = AlloyUtils.getFunctionDefinition(commandResults.get(0), "this_A");
        Set<String> aAtoms = TranslatorUtils.getAtomSet(a);
        assertEquals(1, aAtoms.size());
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

        FunctionDefinition a = AlloyUtils.getFunctionDefinition(commandResults.get(0), "this_A");
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

        FunctionDefinition a = AlloyUtils.getFunctionDefinition(commandResults.get(0), "this_A");
        Set<String> aAtoms = TranslatorUtils.getAtomSet(a);
        assertEquals(2, aAtoms.size());
    }


    @Test
    void oneQuantifier() throws Exception
    {
        String alloy = "sig A {} fact {one x : A | x != none}";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertEquals("sat", commandResults.get(0).satResult);
        FunctionDefinition a = AlloyUtils.getFunctionDefinition(commandResults.get(0), "this_A");
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
        FunctionDefinition a = AlloyUtils.getFunctionDefinition(commandResults.get(0), "this_A");
        Set<String> aAtoms = TranslatorUtils.getAtomSet(a);
        assertEquals(2, aAtoms.size());
    }
}
