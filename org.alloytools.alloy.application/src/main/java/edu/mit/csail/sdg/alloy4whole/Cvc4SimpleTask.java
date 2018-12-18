package edu.mit.csail.sdg.alloy4whole;

import edu.mit.csail.sdg.alloy4.WorkerEngine;


import java.io.*;
import java.util.*;
import java.util.concurrent.TimeUnit;

public class Cvc4SimpleTask implements WorkerEngine.WorkerTask
{
    public static final int TIMEOUT = 300;

    private final Map<String, String> alloyFiles;

    Cvc4SimpleTask(Map<String, String> alloyFiles)
    {
        this.alloyFiles  = alloyFiles;
    }
    @Override
    public void run(WorkerEngine.WorkerCallback workerCallback) throws Exception
    {
        // translate alloy file to smt2 file
        try
        {
            //ToDo: implement the case when there are multiple files
            Iterator<Map.Entry<String, String>> iterator = alloyFiles.entrySet().iterator();

            Map.Entry<String, String> entry = iterator.next();
            String fileName                 = entry.getKey();

            ProcessBuilder  processBuilder  = new ProcessBuilder();
            String [] command        = new String[]{
                    "java",
                    "-jar",
                    "alloy2smt.jar",
//                    "-i",
//                    fileName, // input file
                    "-o",
                    fileName + ".smt2"
            };

            processBuilder.command(command);

            workerCallback.callback("Executing command: " + String.join(" ", command));


            Process process = processBuilder.start();

            OutputStream processInput = process.getOutputStream();

            processInput.write(entry.getValue().getBytes());
            processInput.close();

            if(process.waitFor((long) TIMEOUT, TimeUnit.SECONDS))
            {
                String error = getProcessOutput(process.getErrorStream());

                if(!error.isEmpty())
                {
                    throw new Exception(error);
                }

                workerCallback.callback("Finished translating from alloy to smt2: " + fileName + ".smt2");

                String output = getProcessOutput(process.getInputStream());

                workerCallback.callback("Translation output:" + output);
            }
            else
            {
                workerCallback.callback("Timeout: Translation from ally to smt2 did not finish after " + TIMEOUT  + " seconds");
            }
        }
        catch (Exception exception)
        {
            exception.printStackTrace();
            throw exception;
        }
    }

    private String getProcessOutput(InputStream inputStream)
    {
        StringBuilder stringBuilder = new StringBuilder();

        Scanner scanner = new Scanner(inputStream);

        while(scanner.hasNextLine())
        {
            stringBuilder.append(scanner.nextLine()).append("\n");
        }

        return stringBuilder.toString();
    }
}
