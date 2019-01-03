package edu.mit.csail.sdg.alloy4whole;

import edu.mit.csail.sdg.alloy4.WorkerEngine;
import edu.mit.csail.sdg.alloy4whole.solution.Alloy;
import edu.mit.csail.sdg.ast.Command;

import javax.swing.*;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.List;

public class Cvc4EnumerationTask implements WorkerEngine.WorkerTask
{
    private final String xmlFileName;

    Cvc4EnumerationTask(String xmlFileName)
    {
        this.xmlFileName = xmlFileName;
    }

    @Override
    public void run(WorkerEngine.WorkerCallback workerCallback) throws Exception
    {
        try
        {
            JOptionPane.showMessageDialog(null, xmlFileName);
            // read the solution from the xml file
            Alloy alloy = Alloy.readFromXml(xmlFileName);

            if (alloy.instances.size() == 0)
            {
                throw new Exception("No instance found in the file " + xmlFileName);
            }

            // read the command from the only instance in the file
            String command = alloy.instances.get(0).command;

            List<Command> commands = Cvc4SimpleTask.translation.getCommands();

            int     index;
            for (index = 0; index < commands.size() ; index++)
            {
                if(command.equals(commands.get(index).toString()))
                {
                    JOptionPane.showMessageDialog(null, index);
                }
            }

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
}