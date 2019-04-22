package edu.uiowa.shared;

import edu.uiowa.alloy2smt.Utils;
import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.smtAst.FunctionDefinition;
import edu.uiowa.alloy2smt.translators.Translation;

import java.util.List;

public class TestUtils
{
    public static List<CommandResult> runCVC4(String alloy) throws Exception
    {
        Translation translation = Utils.translate(alloy);
        Cvc4Task task = new Cvc4Task();
        return task.run(translation);
    }

    public static FunctionDefinition getFunctionDefinition(CommandResult commandResult, String name)
    {
        return TranslatorUtils.getFunctionDefinition(commandResult.smtModel, name);
    }
}
