package edu.mit.csail.sdg.alloy4whole;

import edu.mit.csail.sdg.alloy4.Version;
import edu.mit.csail.sdg.alloy4.WorkerEngine;
import edu.mit.csail.sdg.alloy4whole.instances.Alloy;
import edu.mit.csail.sdg.ast.Command;
import edu.uiowa.alloy2smt.Utils;
import edu.uiowa.alloy2smt.smtAst.SmtModel;
import edu.uiowa.alloy2smt.translators.Translation;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.List;
import java.util.Map;

import static edu.mit.csail.sdg.alloy4.A4Preferences.ImplicitThis;

public class Cvc4EnumerationTask implements WorkerEngine.WorkerTask
{
    private final String xmlFileName;
    private Translation translation;
    private boolean executedBefore = false;
    // each enumeration task has its own process
    private Cvc4Process cvc4Process;
    private Alloy alloy;
    private Map<String, String> alloyFiles;
    private int commandIndex;
    private String originalFileName;

    Cvc4EnumerationTask(String xmlFileName) throws Exception
    {
        this.xmlFileName = xmlFileName;
    }

    @Override
    public void run(WorkerEngine.WorkerCallback workerCallback) throws Exception
    {
        try
        {
            if(!executedBefore)
            {
                // read the solution from the xml file
                alloy = Alloy.readFromXml(xmlFileName);
                alloyFiles = alloy.getAlloyFiles();
                if (alloy.instances.size() == 0)
                {
                    throw new Exception("No instance found in the file " + xmlFileName);
                }
                // read the command from the only instance in the file
                String command      = alloy.instances.get(0).command;
                originalFileName    = alloy.instances.get(0).fileName;

                translation = translateToSMT();

                // find the index of the matching command
                List<Command> commands = translation.getCommands();
                for (commandIndex = 0; commandIndex < commands.size() ; commandIndex++)
                {
                    if(command.equals(commands.get(commandIndex).toString()))
                    {
                        break;
                    }
                }

                String smtScript = translation.getSmtScript();

                if (smtScript != null)
                {
                    cvc4Process = Cvc4Process.start(workerCallback);
                    cvc4Process.sendCommand(smtScript);
                    Cvc4Task.setSolverOptions(cvc4Process, translation);
                    // solve the instance
                    solveCommand(commandIndex);

                    executedBefore = true;
                }
                else
                {
                    throw new Exception("No translation found from alloy model to SMT");
                }
            }

            // get a new model and save it
            prepareInstance(commandIndex);

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

    private Translation translateToSMT() throws IOException
    {
        int resolutionMode      = (Version.experimental && ImplicitThis.get()) ? 2 : 1;
        Translation translation = Utils.translate(alloyFiles, originalFileName, resolutionMode);

        File jsonFile = File.createTempFile("tmp", ".mapping.json", new File(Cvc4Task.tempDirectory));

        // output the mapping
        translation.getMapper().writeToJson(jsonFile.getPath());

        return translation;
    }


    private void solveCommand(int index) throws Exception
    {
        String commandTranslation = translation.translateCommand(index);

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
        Command command = translation.getCommands().get(commandIndex);

        SmtModel model = Cvc4Task.parseModel(smtModel);

        File xmlFile        = new File(xmlFileName);

        String xmlFilePath  = xmlFile.getAbsolutePath();

        Cvc4Task.writeModelToAlloyXmlFile(translation.getMapper(), model, xmlFilePath,
                originalFileName, command, alloy.getAlloyFiles());
    }
}