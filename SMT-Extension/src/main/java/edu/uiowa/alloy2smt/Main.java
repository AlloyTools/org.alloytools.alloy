/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt;

import edu.uiowa.alloy2smt.translators.Translation;
import edu.uiowa.alloy2smt.utils.AlloySettings;
import edu.uiowa.smt.printers.SmtLibPrinter;
import org.apache.commons.cli.*;

import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.InvalidPathException;
import java.nio.file.Paths;
import java.util.Formatter;
import java.util.Scanner;

public class Main
{
  public static final String SEP = File.separator;
  public static final String OUTPUT_DIR = System.getProperty("java.io.tmpdir");
  public static final String DEFAULT_OUTPUT_FILE = "output.smt2";

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

  public static void main(String[] args)
  {
    Options options = new Options();
    CommandLineParser commandLineParser = new DefaultParser();

    options.addOption(Option.builder("i").longOpt("input").desc("Input Alloy model").hasArg().build());
    options.addOption(Option.builder("o").longOpt("output").desc("SMT-LIB model output").hasArg().build());

    try
    {
      CommandLine command = commandLineParser.parse(options, args);

      Translation translation;
      String defaultOutputFile;

      if (command.hasOption("i"))
      {
        String inputFile = command.getOptionValue("i").trim();

        if (isValidInputFilePath(inputFile))
        {
          String alloy = new String(Files.readAllBytes(Paths.get(inputFile)), StandardCharsets.UTF_8);
          translation = Utils.translate(alloy, AlloySettings.Default);
          defaultOutputFile = OUTPUT_DIR + SEP + new File(inputFile).getName() + ".smt2";
        }
        else
        {
          throw new Exception("Can not open file " + inputFile);
        }
      }
      else
      {
        StringBuilder stringBuilder = new StringBuilder();
        Scanner scanner = new Scanner(System.in);

        while (scanner.hasNextLine())
        {
          stringBuilder.append(scanner.nextLine()).append("\n");
        }

        translation = Utils.translate(stringBuilder.toString(), AlloySettings.Default);
        defaultOutputFile = DEFAULT_OUTPUT_FILE + ".smt2";
      }

      File outputFile = null;

      if (command.hasOption("o"))
      {
        if (isValidOutputFilePath(command.getOptionValue("o")))
        {
          outputFile = new File(command.getOptionValue("o").trim());
        }
      }
      if (outputFile == null)
      {
        outputFile = new File(defaultOutputFile);
      }
      try (Formatter formatter = new Formatter(outputFile))
      {
        formatter.format("%s\n", translation.getOptimizedSmtScript());

        System.out.println("\n");
        System.out.println(translation.getOptimizedSmtScript());

        // translate all alloy commands
        for (int i = 0; i < translation.getCommands().size(); i++)
        {
          String commandTranslation = translation.getOptimizedSmtScript(i).toString();

          commandTranslation = SmtLibPrinter.PUSH + "\n" + commandTranslation +
              SmtLibPrinter.CHECK_SAT + "\n" + SmtLibPrinter.GET_MODEL + "\n" +
              SmtLibPrinter.POP + "\n";

          formatter.format("%s\n", commandTranslation);
          System.out.println("\n" + commandTranslation);
        }
      }
      System.out.println("\nThe SMT-LIB model was generated at: " + outputFile.getAbsolutePath());
    }
    catch (ParseException exception)
    {
      HelpFormatter formatter = new HelpFormatter();
      formatter.printHelp("java -jar alloy2smt.jar ", options);
    }
    catch (Exception exception)
    {
      exception.printStackTrace();
    }
  }
}
