package edu.uiowa.alloy2smt.translators;

import edu.uiowa.alloy2smt.smt.smtAst.FunctionDefinition;
import edu.uiowa.shared.CommandResult;
import edu.uiowa.shared.TestUtils;
import org.junit.jupiter.api.Test;

import java.util.List;

class FieldTranslatorTests
{
    @Test
    void oneMultiplicity() throws Exception
    {
        String alloy = "sig a {f: a}";
        List<CommandResult> commandResults = TestUtils.runCVC4(alloy);
        FunctionDefinition a = TestUtils.getFunctionDefinition(commandResults.get(0), "this_a");
    }

    @Test
    void oneMultiplicityInt() throws Exception
    {
        String alloy = "sig a in Int {f: a}";
        List<CommandResult> commandResults = TestUtils.runCVC4(alloy);
        FunctionDefinition a = TestUtils.getFunctionDefinition(commandResults.get(0), "this_a");
    }
}




