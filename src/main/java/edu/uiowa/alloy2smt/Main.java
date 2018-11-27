/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 * 
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt;
import java.io.BufferedReader;
import org.apache.commons.cli.*;
import java.util.Formatter;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.file.InvalidPathException;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class Main
{
    public static boolean isValidInputFilePath(String path)
    {
        File inputFile = new File(path);
        
        return inputFile.exists() && inputFile.canRead() && path.endsWith(".als");
    }
    
    public static boolean isValidOutputFilePath(String path) throws IOException
    {
        try 
        {
            Paths.get(path);          
        } 
        catch (InvalidPathException | NullPointerException ex) 
        {
            return false;
        }
        
        File outputFile = new File(path);
        
        if (outputFile.getParentFile() != null) 
        {
          outputFile.getParentFile().mkdirs();
        }
        outputFile.createNewFile();          
        return true;        
    } 
    
    public static void executeCVC4(String cvc4, String fileName, String[] cvc4Flags) throws InterruptedException
    {
        if(cvc4 == null) 
        {
            System.out.println("No CVC4 binary provied!");
            return;
        }        
        if(fileName == null) 
        {
            System.out.println("No input file for CVC4!");
            return;
        }        
        
        File cvc4Binary = new File(cvc4);
        
        if(!cvc4Binary.exists())
        {
            System.out.println("CVC4 binary does not exist at: " + cvc4);
            return;
        }
        if(!cvc4Binary.canExecute())
        {
            System.out.println("CVC4 binary cannot be executed at: " + cvc4);
            return;            
        }
        
        ProcessBuilder  pb          = new ProcessBuilder();
        List<String>    commands    = new ArrayList();
        
        commands.add(cvc4);
        commands.add(fileName);
        
        if(cvc4Flags != null)
        {
            commands.addAll(Arrays.asList(cvc4Flags));               
        } 
                
        try {
            pb.command(commands);
//            System.out.println(output(process.getInputStream()));    
            System.out.println("**************************************** Checking with CVC4 ****************************************");            
            System.out.println("\nCommand executed: " + pb.command());
            Process process = pb.start();
            int errCode = process.waitFor();                 
            System.out.println("Any errors? " + (errCode == 0 ? "No" : "Yes"));
            System.out.println("CVC4 Output:\n" + output(process.getInputStream()));    
            System.out.println("********************************************************************************************************\n");                          
        } catch (IOException ex) {            
        }         
    }    
    
    private static String output(InputStream inputStream) throws IOException 
    {
        StringBuilder sb = new StringBuilder();
        BufferedReader br = null;
        try {
            br = new BufferedReader(new InputStreamReader(inputStream));
            String line = null;
            while ((line = br.readLine()) != null) 
            {
                sb.append(line).append(System.getProperty("line.separator"));
            }
        } 
        finally 
        {
            br.close();
        }
        return sb.toString();
    }     
    
    public static void main(String[] args)
    {
        Options             options             = new Options();
        CommandLineParser   commandLineParser   = new DefaultParser();        
        
        options.addOption(Option.builder("i").longOpt("input").desc("Input Alloy model").hasArg().required().build());
        options.addOption(Option.builder("o").longOpt("output").desc("SMT-LIB model output").hasArg().build());
        options.addOption(Option.builder("b").longOpt("cvc4-binary").desc("CVC4 binary path").hasArg().build());
        options.addOption(Option.builder("f").longOpt("cvc4-flags").desc("CVC4 flags").hasArgs().build());
        options.addOption(Option.builder("a").longOpt("assertion").desc("The assertion to be checked").hasArg().build());
        
        try
        {
            CommandLine command = commandLineParser.parse(options, args);
            
            if (command.hasOption("i"))
            {
                String  cvc4        = null;
                String  inputFile   = command.getOptionValue("i").trim();                             

                if(isValidInputFilePath(inputFile))
                {
                    File    outputFile      = null;   
                    File    alloyFile       = new File(inputFile);
                    String  cvc4Binary      = command.hasOption("b")?command.getOptionValue("b").trim():null;
                    String  assertion       = command.hasOption("a")?command.getOptionValue("a").trim():null;
                    String  outputDir       = System.getProperty("java.io.tmpdir");                    
                    String  output          = Utils.translateFromFile(alloyFile.getAbsolutePath(), assertion);                    
                    String  outputFilePath  = outputDir + File.separator + alloyFile.getName() + ".smt2";
                    
                    if(command.hasOption("o"))
                    {                        
                        if(isValidOutputFilePath(command.getOptionValue("o"))) 
                        {
                            outputFile = new File(command.getOptionValue("o").trim());                      
                        }                          
                    }
                    if(outputFile == null)
                    {
                        outputFile = new File(outputFilePath);                      
                    }
                    try (Formatter formatter = new Formatter(outputFile)) 
                    {
                        formatter.format("%s", output);
                    }
                    
                    // Execute CVC4 on the output file
                    executeCVC4(cvc4Binary, outputFile.getAbsolutePath(), command.hasOption("f")?command.getOptionValues('f'):null);
                    System.out.println("\n\n\n");
                    System.out.println(output);                    
                    System.out.println("The SMT-LIB model is generated at: " + outputFile.getAbsolutePath());
                }
                else
                {
                    throw new Exception("Can not open file " + inputFile);
                }
            }
            else
            {
                throw new ParseException("");
            }
        }
        catch (ParseException exception)
        {
            HelpFormatter formatter = new HelpFormatter();
            formatter.printHelp( "java -jar alloy2smt.jar ", options );
        }
        catch (Exception exception)
        {
            exception.printStackTrace();
        }
    }
}
