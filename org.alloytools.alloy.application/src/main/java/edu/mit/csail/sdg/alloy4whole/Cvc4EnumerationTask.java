package edu.mit.csail.sdg.alloy4whole;

import edu.mit.csail.sdg.alloy4.Version;
import edu.mit.csail.sdg.alloy4.WorkerEngine;
import edu.mit.csail.sdg.alloy4whole.instances.Alloy;
import edu.mit.csail.sdg.ast.Command;
import edu.uiowa.alloy2smt.Utils;
import edu.uiowa.smt.AbstractTranslator;
import edu.uiowa.smt.printers.SmtLibPrettyPrinter;
import edu.uiowa.smt.smtAst.SmtModel;
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
            if(! xmlFileName.equals(Cvc4Task.lastXmlFile))
            {
                workerCallback.callback(new Object[]{"pop", "You can only enumerate the solutions of the last executed command."});
                return;
            }

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

            // (check-sat)
            String result = Cvc4Task.cvc4Process.sendCommand(SmtLibPrettyPrinter.CHECK_SAT);
            if(result != null)
            {
                switch (result)
                {
                    case "sat":
                        // get a new model and save it
                        prepareInstance(commandIndex);
                        // tell alloy user interface that the last instance has changed
                        workerCallback.callback(new Object[]{"declare", xmlFileName});
                        break;
                    case "unsat":
                        workerCallback.callback(new Object[]{"pop", "There are no more satisfying instances.\n\n" + "Note: due to symmetry breaking and other optimizations,\n" + "some equivalent solutions may have been omitted."});
                        break;
                    default:
                        workerCallback.callback(new Object[]{"pop", "CVC4 solver returned unknown."});
                }
            }
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
        return translation;
    }

    private void prepareInstance(int commandIndex) throws Exception
    {
        String smtModel     = Cvc4Task.cvc4Process.sendCommand(SmtLibPrettyPrinter.GET_MODEL);
        Command command     = translation.getCommands().get(commandIndex);

        SmtModel model      = Cvc4Task.parseModel(smtModel);

        File xmlFile        = new File(xmlFileName);

        String xmlFilePath  = xmlFile.getAbsolutePath();

        Cvc4Task.writeModelToAlloyXmlFile(translation, model, xmlFilePath,
                originalFileName, command, alloy.getAlloyFiles());
    }
}