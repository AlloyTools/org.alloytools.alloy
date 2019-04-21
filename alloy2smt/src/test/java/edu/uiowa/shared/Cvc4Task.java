package edu.uiowa.shared;

import edu.mit.csail.sdg.ast.Command;
import edu.uiowa.alloy2smt.smt.smtAst.SmtModel;
import edu.uiowa.alloy2smt.smt.parser.SmtModelVisitor;
import edu.uiowa.alloy2smt.smt.parser.antlr.SmtLexer;
import edu.uiowa.alloy2smt.smt.parser.antlr.SmtParser;
import edu.uiowa.alloy2smt.translators.Translation;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

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

            setSolverOptions(cvc4Process, translation);

            // surround each command except the last one with (push) and (pop)
            for (int index = 0; index < translation.getCommands().size(); index++)
            {
                // (push)
                cvc4Process.sendCommand(Translation.PUSH);
                CommandResult commandResult = solveCommand(index, translation);
                // (pop)
                cvc4Process.sendCommand(Translation.POP);
                commandResults.add(commandResult);
            }
            return commandResults;
        }
        return new ArrayList<>();
    }

    public static String setSolverOptions(Cvc4Process cvc4Process, Translation translation) throws IOException
    {
        Map<String, String> options = new HashMap<>();
        options.put("tlimit", "30000");
        String script = translation.translateOptions(options);
        cvc4Process.sendCommand(script);
        return script;
    }

    private CommandResult solveCommand(int index, Translation translation) throws Exception
    {
        String commandTranslation = translation.translateCommand(index);
        Command command = translation.getCommands().get(index);
        String result = cvc4Process.sendCommand(commandTranslation + Translation.CHECK_SAT);

        CommandResult commandResult = new CommandResult();
        commandResult.index         = index;
        commandResult.command       = command;
        commandResult.result        = result;

        if(result.equals("sat"))
        {
            String model = cvc4Process.sendCommand(Translation.GET_MODEL);
            commandResult.smtModel = parseModel(model);
        }
        return commandResult;
    }

    public SmtModel parseModel(String model)
    {
        CharStream charStream = CharStreams.fromString(model);

        SmtLexer lexer = new SmtLexer(charStream);
        CommonTokenStream tokenStream = new CommonTokenStream(lexer);
        SmtParser parser = new SmtParser(tokenStream);

        ParseTree tree =  parser.model();
        SmtModelVisitor visitor = new SmtModelVisitor();

        SmtModel smtModel = (SmtModel) visitor.visit(tree);

        return  smtModel;
    }
}
