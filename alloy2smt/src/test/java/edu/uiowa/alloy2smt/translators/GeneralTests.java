package edu.uiowa.alloy2smt.translators;

import edu.uiowa.alloy2smt.utils.AlloyUtils;
import edu.uiowa.alloy2smt.utils.CommandResult;
import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.smtAst.FunctionDefinition;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.*;

class GeneralTests
{
    @Test
    public void test1() throws Exception
    {
        String alloy =  "sig A {r: A -> A}\n" +
                "\n" +
                "fact {\n" +
                "#r = 2\n" +
                "}\n" +
                "run {} for 4 Int, 7 seq";

        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy);
        assertEquals("sat", commandResults.get(0).satResult);

        FunctionDefinition A = TranslatorUtils.getFunctionDefinition(commandResults.get(0).smtModel, "this_A");
        Set<String> atoms = TranslatorUtils.getAtomSet(A);
        assertTrue(2 <= atoms.size());

        FunctionDefinition r = TranslatorUtils.getFunctionDefinition(commandResults.get(0).smtModel, "this_A_r");
        Set<List<String>> tuples = TranslatorUtils.getAtomRelation(r);
        assertEquals(2, tuples.size());
    }
}
