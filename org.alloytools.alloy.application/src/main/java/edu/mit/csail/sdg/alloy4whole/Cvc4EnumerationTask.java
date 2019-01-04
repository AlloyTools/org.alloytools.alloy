package edu.mit.csail.sdg.alloy4whole;

import edu.mit.csail.sdg.alloy4.WorkerEngine;
import edu.mit.csail.sdg.alloy4whole.solution.Alloy;
import edu.mit.csail.sdg.ast.Command;
import edu.uiowa.alloy2smt.smtAst.SmtModel;
import edu.uiowa.alloy2smt.translators.Translation;

import java.io.File;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.List;

public class Cvc4EnumerationTask implements WorkerEngine.WorkerTask
{
    private final String xmlFileName;
    private static boolean started = false;
    private static Cvc4Process cvc4Process;

    Cvc4EnumerationTask(String xmlFileName)
    {
        this.xmlFileName = xmlFileName;
    }

    @Override
    public void run(WorkerEngine.WorkerCallback workerCallback) throws Exception
    {
        try
        {
            // read the solution from the xml file
            Alloy alloy = Alloy.readFromXml(xmlFileName);

            if (alloy.instances.size() == 0)
            {
                throw new Exception("No instance found in the file " + xmlFileName);
            }

            // read the command from the only instance in the file
            String command = alloy.instances.get(0).command;

            // find the index of the matching command
            List<Command> commands = Cvc4Task.translation.getCommands();
            int index;
            for (index = 0; index < commands.size() ; index++)
            {
                if(command.equals(commands.get(index).toString()))
                {
                    break;
                }
            }

            // start cvc4 if it is not started already
            //ToDo; handle the case of new execution
            if(! started)
            {
                String smtScript = Cvc4Task.translation.getSmtScript();

                if (smtScript != null)
                {
                    cvc4Process = Cvc4Process.start(workerCallback);

                    cvc4Process.sendCommand(smtScript);

                    Cvc4Task.setSolverOptions(cvc4Process);

                    // solve the instance
                    solveCommand(index);

                    started = true;
                }
                else
                {
                    throw new Exception("No translation found from alloy model to SMT");
                }
            }

            // get a new model and save it
            prepareInstance(index);

            // tell alloy user interface that the last instance has changed
            workerCallback.callback(new Object[]{"declare", xmlFileName});
        }
        catch (Exception exception)
        {
            StringWriter stringWriter = new StringWriter();
            exception.printStackTrace(new PrintWriter(stringWriter));
            throw new Exception(stringWriter.toString());
        }
    }

    private void solveCommand(int index) throws Exception
    {
        String commandTranslation = Cvc4Task.translation.translateCommand(index);

        // (check-sat)
        String result = cvc4Process.sendCommand(commandTranslation + Translation.CHECK_SAT);

        if(result != null)
        {
            switch (result)
            {
                case "sat":
                    break;
                case "unsat":
                    {
                        throw new Exception("The result is unsat\n");
                    }
                default:
                    throw new Exception("The result is unknown\n");
            }
        }
        else
        {
            throw new Exception("No result returned from cvc4\n");
        }

        // get the initial model
        cvc4Process.sendCommand(Translation.GET_MODEL);
    }

    private void prepareInstance(int commandIndex) throws Exception
    {
        String smtModel = cvc4Process.sendCommand(Translation.GET_MODEL);
        Command command = Cvc4Task.translation.getCommands().get(commandIndex);

        SmtModel model = Cvc4Task.parseModel(smtModel);

        File xmlFile        = new File(xmlFileName);

        String xmlFilePath  = xmlFile.getAbsolutePath();

        Cvc4Task.writeModelToAlloyXmlFile(Cvc4Task.translation.getMapper(), model, xmlFilePath,
                Cvc4Task.originalFileName, command);
    }
}