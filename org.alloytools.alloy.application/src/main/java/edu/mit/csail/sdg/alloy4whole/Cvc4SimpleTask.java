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
            for(Map.Entry<String,String> entry : alloyFiles.entrySet())
            {
                try (PrintWriter printWriter = new PrintWriter(entry.getKey())) {
                    printWriter.print(entry.getValue());
                }
            }

            //ToDo: implement the case when there are multiple files
            Iterator<Map.Entry<String, String>> iterator = alloyFiles.entrySet().iterator();

            String fileName = iterator.next().getKey();

            ProcessBuilder  processBuilder  = new ProcessBuilder();
            String [] command        = new String[]{
                    "java",
                    "-jar",
                    "alloy2smt.jar",
                    "-i",
                    fileName, // input file
                    "-o",
                    fileName + ".smt2"
            };

            processBuilder.command(command);

            workerCallback.callback("Executing command: " + String.join(" ", command));

            Process process = processBuilder.start();

            if(process.waitFor((long) TIMEOUT, TimeUnit.SECONDS))
            {
                workerCallback.callback("Finished translating from alloy to smt2: " + fileName + ".smt2");

                String error = getProcessOutput(process.getErrorStream());

                if(!error.isEmpty())
                {
                    throw new Exception(error);
                }

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
            workerCallback.callback(exception.getMessage());
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
