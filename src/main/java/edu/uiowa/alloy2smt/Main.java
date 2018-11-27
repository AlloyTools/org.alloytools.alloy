/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 * 
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt;
import org.apache.commons.cli.*;
import java.util.Formatter;
import java.io.File;
import java.io.IOException;
import java.nio.file.InvalidPathException;
import java.nio.file.Paths;

public class Main
{
    public static boolean isValidInputFilePath(String path)
    {
        File inputFile = new File(path);
        
        if(inputFile.exists() && inputFile.canRead() && path.endsWith(".als"))
        {
            return true;
        }
        return false;
    }
    
    public static boolean isValidOutputFilePath(String path) throws IOException
    {
        try {
            Paths.get(path);          
        } catch (InvalidPathException | NullPointerException ex) {
            return false;
        }
        File outputFile = new File(path);
        if (outputFile.getParentFile() != null) {
          outputFile.getParentFile().mkdirs();
        }
        outputFile.createNewFile();          
        return true;        
    }    
    
    public static void main(String[] args)
    {
        Options             options             = new Options();
        CommandLineParser   commandLineParser   = new DefaultParser();        
        
        options.addOption(Option.builder("i").longOpt("input").desc("Input Alloy model").hasArg().required().build());
        options.addOption(Option.builder("o").longOpt("output").desc("SMT-LIB model output").hasArg().build());
        options.addOption(Option.builder("b").longOpt("cvc4-binary").desc("CVC4 binary path").hasArg().build());
        options.addOption(Option.builder("f").longOpt("cvc4-flags").desc("CVC4 flags").hasArgs().build());
        
        try
        {
            CommandLine command = commandLineParser.parse(options, args);
            
            if (command.hasOption("i"))
            {
                String  cvc4            = null;
                String  inputFile       = command.getOptionValue("i");
                File    file            = new File(inputFile);                

                if(isValidInputFilePath(inputFile))
                {
                    File    outputFile      = null;                    
                    String  outputDir       = System.getProperty("java.io.tmpdir");                    
                    String  output          = Utils.translateFromFile(file.getAbsolutePath());                    
                    String  outputFilePath  = outputDir + File.separator + file.getName() + ".smt2";
                    
                    if(command.hasOption("o"))
                    {                        
                        if(isValidOutputFilePath(command.getOptionValue("o"))) 
                        {
                            outputFile = new File(command.getOptionValue("o"));                      
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
                    System.out.println(output);
                    System.out.println("\n\n\n");
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
