package edu.uiowa.alloy2smt.utils;

import edu.mit.csail.sdg.ast.Command;
import edu.uiowa.alloy2smt.Utils;
import edu.uiowa.alloy2smt.translators.Translation;
import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.smtAst.FunctionDefinition;

import java.util.List;

public class AlloyUtils
{
    public static List<CommandResult> runAlloyString(String alloy, boolean includeScope) throws Exception
    {
        Translation translation = Utils.translate(alloy);
        Cvc4Task task = new Cvc4Task();
        return task.run(translation, includeScope);
    }

    public static List<CommandResult> runAlloyFile(String fileName, boolean includeScope) throws Exception
    {
        Translation translation = Utils.translateFromFile(fileName);
        Cvc4Task task = new Cvc4Task();
        return task.run(translation, includeScope);
    }

    public static FunctionDefinition getFunctionDefinition(CommandResult commandResult, String name)
    {
        return TranslatorUtils.getFunctionDefinition(commandResult.smtModel, name);
    }
}
