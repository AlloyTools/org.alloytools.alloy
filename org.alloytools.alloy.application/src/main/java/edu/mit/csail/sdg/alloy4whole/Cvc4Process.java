package edu.mit.csail.sdg.alloy4whole;

import edu.mit.csail.sdg.alloy4.WorkerEngine;

import java.io.File;
import java.io.IOException;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;


public class Cvc4Process
{

    public static final String OS       = System.getProperty("os.name");
    public static final String SEP      = File.separator;
    public static final String BIN_PATH = System.getProperty("user.dir")+SEP;

    private Process process;
    private Scanner scanner;
    private OutputStream outputStream;
    private WorkerEngine.WorkerCallback workerCallback;
    private boolean firstRead = true;



    private Cvc4Process(Process process, WorkerEngine.WorkerCallback workerCallback)
    {
        this.process        = process;
        this.scanner        = new Scanner(process.getInputStream());
        this.outputStream   = process.getOutputStream();
        this.workerCallback = workerCallback;

    }

    public static Cvc4Process start(WorkerEngine.WorkerCallback workerCallback) throws Exception
    {
        String cvc4;

        if(OS.startsWith("Windows"))
        {
            cvc4 = BIN_PATH + "cvc4_win64.exe";
        }
        else if(OS.startsWith("Linux"))
        {
            cvc4 = BIN_PATH + "cvc4_linux";
        }
        else
        {
            throw new Exception("No CVC4 binary available for the OS: " + OS);
        }

        File cvc4Binary = new File(cvc4);

        if(!cvc4Binary.exists())
        {
            throw new Exception("CVC4 binary does not exist at: " + cvc4);
        }
        if(!cvc4Binary.canExecute())
        {
            throw new Exception("CVC4 binary cannot be executed at: " + cvc4);
        }

        ProcessBuilder  processBuilder = new ProcessBuilder();
        List<String> command       = new ArrayList<>();

        command.add(cvc4);

        // tell cvc4 the input language is smt2
        command.add("--lang");
        command.add("smtlib2.6");
//        command.add("--print-success");

        processBuilder.command(command);

        workerCallback.callback(new Object[]{"","Executing command: " + String.join(" ", command) + "\n\n"});

        processBuilder.redirectErrorStream(true);
        Process process = processBuilder.start();


        return new Cvc4Process(process, workerCallback);
    }

    public void sendCommand(String command) throws IOException
    {
        outputStream.write((command + "\n").getBytes());
        outputStream.flush();
    }

    public String receiveOutput() throws IOException
    {
        String line = "";

        this.sendCommand("(echo success)\n");
        String output = "";
        while(scanner.hasNextLine())
        {
            line = scanner.nextLine();

            if(line.equals("success"))
            {
                return output.trim();
            }
            output += line + "\n";
        }
        return line;
    }

    public void destroy()
    {
        process.destroyForcibly();
    }
}
