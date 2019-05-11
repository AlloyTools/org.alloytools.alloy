package edu.uiowa.alloy2smt.translators;

import edu.uiowa.smt.smtAst.FunctionDefinition;
import edu.uiowa.alloy2smt.utils.CommandResult;
import edu.uiowa.alloy2smt.utils.AlloyUtils;
import org.junit.jupiter.api.Test;

import java.util.List;

class FieldTranslatorTests
{
    @Test
    void oneMultiplicity() throws Exception
    {
        String alloy = "sig a {f: a}";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy);
        FunctionDefinition a = AlloyUtils.getFunctionDefinition(commandResults.get(0), "this_a");
    }

    @Test
    void oneMultiplicityInt() throws Exception
    {
        String alloy = "sig a in Int {f: a}";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy);
        FunctionDefinition a = AlloyUtils.getFunctionDefinition(commandResults.get(0), "this_a");
    }
}




