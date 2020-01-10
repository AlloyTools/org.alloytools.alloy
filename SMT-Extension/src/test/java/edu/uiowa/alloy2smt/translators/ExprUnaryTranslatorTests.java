package edu.uiowa.alloy2smt.translators;

import edu.uiowa.alloy2smt.utils.AlloyUtils;
import edu.uiowa.alloy2smt.utils.CommandResult;
import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.smtAst.FunctionDefinition;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.assertFalse;

public class ExprUnaryTranslatorTests
{
    @Test
    void some() throws Exception
    {
        String alloy = "sig A {} fact f{some A}";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertEquals("sat", commandResults.get(0).satResult);
        FunctionDefinition a = AlloyUtils.getFunctionDefinition(commandResults.get(0), "this/A");
        Set<String> set = TranslatorUtils.getAtomSet(a);
        assertFalse(set.isEmpty());
    }

    @Test
    void no() throws Exception
    {
        String alloy = "sig A {} fact f{no A}";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertEquals("sat", commandResults.get(0).satResult);
        FunctionDefinition a = AlloyUtils.getFunctionDefinition(commandResults.get(0), "this/A");
        Set<String> set = TranslatorUtils.getAtomSet(a);
        assertTrue(set.isEmpty());
    }

    @Test
    void lone1() throws Exception
    {
        String alloy = "sig A {} fact f{lone A and no A}";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertEquals("sat", commandResults.get(0).satResult);
        FunctionDefinition a = AlloyUtils.getFunctionDefinition(commandResults.get(0), "this/A");
        Set<String> set = TranslatorUtils.getAtomSet(a);
        assertTrue(set.isEmpty());
    }

    @Test
    void lone2() throws Exception
    {
        String alloy = "sig A {} fact f{lone A and some A}";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertEquals("sat", commandResults.get(0).satResult);
        FunctionDefinition a = AlloyUtils.getFunctionDefinition(commandResults.get(0), "this/A");
        Set<String> set = TranslatorUtils.getAtomSet(a);
        assertFalse(set.isEmpty());
    }

    @Test
    void loneOf1() throws Exception
    {
        String alloy = "sig A {} fact f{all x: lone A | some x}";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertEquals("unsat", commandResults.get(0).satResult);
    }

    @Test
    void loneOf2() throws Exception
    {
        String alloy = "some sig A {} fact f{all x: lone A | no x}";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertEquals("unsat", commandResults.get(0).satResult);
    }

    @Test
    void loneOf3() throws Exception
    {
        String alloy = "sig A {} fact f{all x: lone A | some x or no x}";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertEquals("sat", commandResults.get(0).satResult);
    }
}
