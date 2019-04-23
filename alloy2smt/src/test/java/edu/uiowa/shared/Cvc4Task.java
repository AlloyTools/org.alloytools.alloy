package edu.uiowa.shared;

import edu.mit.csail.sdg.ast.Command;
import edu.uiowa.smt.AbstractTranslator;
import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.cvc4.Cvc4Process;
import edu.uiowa.alloy2smt.translators.Translation;

import java.util.ArrayList;
import java.util.List;

public class Cvc4Task
{
    public Cvc4Process cvc4Process;
    public List<CommandResult> run(Translation translation) throws Exception
    {
        List<CommandResult> commandResults = new ArrayList<>();
        String smtScript = translation.getSmtScript();
        if (smtScript != null)
        {
            cvc4Process = Cvc4Process.start();

            cvc4Process.sendCommand(smtScript);

            TranslatorUtils.setSolverOptions(cvc4Process);

            // surround each command except the last one with (push) and (pop)
            for (int index = 0; index < translation.getCommands().size(); index++)
            {
                // (push)
                cvc4Process.sendCommand(AbstractTranslator.PUSH);
                CommandResult commandResult = solveCommand(index, translation);
                // (pop)
                cvc4Process.sendCommand(AbstractTranslator.POP);
                commandResults.add(commandResult);
            }
            return commandResults;
        }
        return new ArrayList<>();
    }

    private CommandResult solveCommand(int index, Translation translation) throws Exception
    {
        String commandTranslation = translation.translateCommand(index);
        Command command = translation.getCommands().get(index);
        String result = cvc4Process.sendCommand(commandTranslation + AbstractTranslator.CHECK_SAT);

        String smt = translation.getSmtScript() + commandTranslation + AbstractTranslator.CHECK_SAT;
        CommandResult commandResult = new CommandResult(index, command, smt, result);

        if(result.equals("sat"))
        {
            String model = cvc4Process.sendCommand(AbstractTranslator.GET_MODEL);
            commandResult.smtModel = TranslatorUtils.parseModel(model);
        }
        return commandResult;
    }
}
