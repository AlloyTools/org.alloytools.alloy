package edu.uiowa.alloy2smt;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.uiowa.alloy2smt.printers.SMTLibPrettyPrinter;
import edu.uiowa.alloy2smt.smtAst.SMTAst;
import org.apache.commons.cli.*;
import java.util.Formatter;
import java.io.File;

public class Main
{
    public static void main(String[] args)
    {
        System.out.println("Alloy to SMT");

        Options options = new Options();

        options.addOption(Option.builder("i").longOpt("input").hasArg().required().build());
        options.addOption(Option.builder("o").longOpt("output").hasArg().build());

        CommandLineParser commandLineParser = new DefaultParser();
        try
        {
            CommandLine command = commandLineParser.parse(options, args);
            if (command.hasOption("i"))
            {
                String inputFile  = command.getOptionValue("i");
                File file = new File(inputFile);

                if((file.exists() && file.canRead()))
                {
                    CompModule alloyModel = CompUtil.parseEverything_fromFile(null, null,
                            file.getAbsolutePath());

                    Alloy2SMTTranslator translator = new Alloy2SMTTranslator();
                    SMTAst root = translator.execute();
                    SMTLibPrettyPrinter printer = new SMTLibPrettyPrinter(root);
                    String output = printer.print();

                    if(command.hasOption("o"))
                    {
                        //ToDo: validation
                        File outputFile = new File(command.getOptionValue("o"));
                        Formatter formatter = new Formatter(outputFile);
                        formatter.format("%s", output);
                        formatter.close();
                    }
                    else
                    {
                        System.out.println(output);
                    }
                }
                else
                {
                    throw new Exception("Can not open file " + file.getName());
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
