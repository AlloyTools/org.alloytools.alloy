package edu.uiowa.smt.parser;

import edu.uiowa.alloy2smt.utils.AlloyUtils;
import edu.uiowa.alloy2smt.utils.CommandResult;
import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.smtAst.FunctionDefinition;
import org.junit.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class SmtLibParserTests
{
    @Test
    public void GT() throws Exception
    {
        String alloy = "sig A, A' {} fact {#A = 2 and #A' = 3}";

        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertTrue(commandResults.size() == 1);
        assertEquals("sat", commandResults.get(0).satResult);
        FunctionDefinition a = AlloyUtils.getFunctionDefinition(commandResults.get(0), "this/a");
        int aValue = TranslatorUtils.getInt(a);
        assertTrue(aValue > 2);
    }
}
