package edu.uiowa.shared;

import edu.uiowa.alloy2smt.Utils;
import edu.uiowa.alloy2smt.smtAst.FunctionDefinition;
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
        FunctionDefinition definition = (FunctionDefinition) commandResult.smtModel
                .getFunctions().stream()
                .filter(f -> f.getName().equals(name)).findFirst().get();
        definition = commandResult.smtModel.evaluateUninterpretedInt(definition);
        return definition;
    }
}
