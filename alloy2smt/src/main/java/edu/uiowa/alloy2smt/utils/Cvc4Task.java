package edu.uiowa.alloy2smt.utils;

import edu.mit.csail.sdg.ast.Command;
import edu.uiowa.alloy2smt.translators.Translation;
import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.cvc4.Cvc4Process;
import edu.uiowa.smt.printers.SmtLibPrettyPrinter;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class Cvc4Task
{
    public Cvc4Process cvc4Process;

    private int timeout;

    public Cvc4Task(int timeout)
    {
        this.timeout = timeout;
    }

    public Cvc4Task()
    {
        this.timeout = 25000;
    }

    public List<CommandResult> run(Translation translation, boolean includeScope) throws Exception
    {
        List<CommandResult> commandResults = new ArrayList<>();
        String smtScript = translation.getSmtScript();
        if (smtScript != null)
        {
            cvc4Process = Cvc4Process.start();

            cvc4Process.sendCommand(smtScript);

            setSolverOptions(cvc4Process);

            // surround each command except the last one with (push) and (pop)
            for (int index = 0; index < translation.getCommands().size(); index++)
            {
                // (push)
                cvc4Process.sendCommand(SmtLibPrettyPrinter.PUSH);
                CommandResult commandResult = solveCommand(index, includeScope, translation);
                // (pop)
                cvc4Process.sendCommand(SmtLibPrettyPrinter.POP);
                commandResults.add(commandResult);
            }
            return commandResults;
        }
        return new ArrayList<>();
    }

    public CommandResult run(Translation translation, boolean includeScope, int commandIndex ) throws Exception
    {
        String smtScript = translation.getSmtScript();
        cvc4Process = Cvc4Process.start();

        cvc4Process.sendCommand(smtScript);

        setSolverOptions(cvc4Process);

        CommandResult commandResult = solveCommand(commandIndex, includeScope, translation);

        return commandResult;
    }

    public String setSolverOptions(Cvc4Process cvc4Process) throws IOException
    {
        Map<String, String> options = new HashMap<>();
        options.put("tlimit", Integer.toString(timeout));
        String script = TranslatorUtils.translateOptions(options);
        cvc4Process.sendCommand(script);
        return script;
    }

    private CommandResult solveCommand(int index, boolean includeScope, Translation translation) throws Exception
    {
        String commandTranslation = translation.translateCommand(index, includeScope);
        Command command = translation.getCommands().get(index);
        String result = cvc4Process.sendCommand(commandTranslation + SmtLibPrettyPrinter.CHECK_SAT);

        String smt = translation.getSmtScript() + commandTranslation + SmtLibPrettyPrinter.CHECK_SAT;
        CommandResult commandResult = new CommandResult(index, command, smt, result);

        if (result.equals("sat"))
        {
            commandResult.model = cvc4Process.sendCommand(SmtLibPrettyPrinter.GET_MODEL);
            commandResult.smtModel = commandResult.parseModel(commandResult.model);
        }
        return commandResult;
    }
}
