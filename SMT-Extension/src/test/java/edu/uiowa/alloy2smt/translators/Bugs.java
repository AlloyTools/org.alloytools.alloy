package edu.uiowa.alloy2smt.translators;

import edu.uiowa.alloy2smt.utils.AlloyUtils;
import edu.uiowa.alloy2smt.utils.CommandResult;
import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.smtAst.FunctionDefinition;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class Bugs
{
    @Test
    public void test1() throws Exception
    {
        String alloy =  "sig a in Int {} one sig a0 in a {}";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertEquals("sat", commandResults.get(0).satResult);

        FunctionDefinition A = TranslatorUtils.getFunctionDefinition(commandResults.get(0).smtModel, "this/a");
        Set<Integer> atoms = TranslatorUtils.getIntSet(A);
        assertEquals(1, atoms.size());
    }
}
