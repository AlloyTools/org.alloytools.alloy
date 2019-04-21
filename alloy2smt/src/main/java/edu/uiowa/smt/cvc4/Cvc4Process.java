package edu.uiowa.smt.cvc4;

import java.io.File;
import java.io.IOException;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import java.util.Scanner;


public class Cvc4Process
{

    public static final String OS       = System.getProperty("os.name");
    public static final String SEP      = File.separator;
    public static final String BIN_PATH = ".." + SEP + "bin" + SEP;

    private Process process;
    private Scanner scanner;
    private OutputStream outputStream;

    private Cvc4Process(Process process)
    {
        this.process        = process;
        this.scanner        = new Scanner(process.getInputStream());
        this.outputStream   = process.getOutputStream();
    }

    public static Cvc4Process start() throws Exception
    {
        String cvc4;

        if(onWindows())
        {
            cvc4 = BIN_PATH + "cvc4_win64.exe";
        }
        else if(onMac())
        {
            cvc4 = BIN_PATH + "cvc4_mac";
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

        processBuilder.command(command);
        processBuilder.redirectErrorStream(true);
        Process process = processBuilder.start();

        return new Cvc4Process(process);
    }

    public String sendCommand(String command) throws IOException
    {
        outputStream.write((command + "\n").getBytes());
        outputStream.flush();
        return receiveOutput();
    }

    private String receiveOutput() throws IOException
    {
        String line = "";
        outputStream.write(("(echo success)\n").getBytes());
        outputStream.flush();

        StringBuilder output = new StringBuilder();

        while(scanner.hasNextLine())
        {
            line = scanner.nextLine();

            if(line.equals("success"))
            {
                return output.toString().trim();
            }
            output.append(line).append("\n");
        }
        return line;
    }

    public void destroy()
    {
        process.destroyForcibly();
    }

    private static boolean onWindows()
    {
        return System.getProperty("os.name").toLowerCase(Locale.US).startsWith("windows");
    }
    private static boolean onMac()
    {
        return System.getProperty("mrj.version") != null || System.getProperty("os.name").toLowerCase(Locale.US).startsWith("mac ");
    }
}
