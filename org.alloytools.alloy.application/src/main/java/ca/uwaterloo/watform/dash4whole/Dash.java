package ca.uwaterloo.watform.dash4whole;

import java.util.*;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.Files;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;

import edu.mit.csail.sdg.alloy4.Version;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4viz.VizGUI;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

import ca.uwaterloo.watform.core.DashOptions;
import ca.uwaterloo.watform.core.DashErrors;
// import ca.uwaterloo.watform.parser.DashUtil;
import ca.uwaterloo.watform.core.DashUtilFcns;
import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.mainfunctions.MainFunctions;




public class Dash {

   @SuppressWarnings("resource" )

   public static void executeCommands(CompModule c, Integer cmdnum, A4Reporter rep) {
        // Choose some default options for how you want to execute the commands
        A4Options options = new A4Options();

        List<Command> commands = c.getAllCommands();
        // this is an annoying way to convert a list to an array
        Integer i = 1;
        for (Command cmd : commands) { 
            if (i == cmdnum | cmdnum == 0) {
                System.out.println("Executing command: " + cmd);
                A4Solution ans = null;
                try {
                    ans = MainFunctions.executeCommand(cmd,c,rep, options);
                } catch (Exception e) {
                    DashUtilFcns.handleException(e);
                }
                if (ans.satisfiable()) {                  
                    if (cmd.expects == 1) 
                        System.out.println("Result: SAT (CORRECT)");
                    else if (cmd.expects == 0)
                        System.out.println("Result: SAT (INCORRECT)");
                    else
                        System.out.println("Result: SAT (nothing expected)");
                } else {
                    if (cmd.expects == 0) 
                        System.out.println("Result: UNSAT (CORRECT)");
                    else if (cmd.expects == 1)
                        System.out.println("Result: UNSAT (INCORRECT)");
                    else
                        System.out.println("Result: UNSAT (nothing expected)");
                }

            }
            i++;
        }
        if (cmdnum >= i) {
            System.err.println("Command number: " + cmdnum + " does not exist in file");
        }
   }

   public static void main(String args[]) throws Exception { 

        if(args.length == 0) {
            //System.out.println("Arguments: (-m traces|tcmc|electrum) (-single) (-reach) (-c #) (-p) (-t) (-r) filename(s)");
            System.out.println("Arguments: (-m traces|tcmc|electrum) (-c #) (-p) (-t) (-r) filename(s)");

            System.out.println("-m traces|tcmc|electrum is verification method");
            //System.out.println("-single includes single event input fact");
            //System.out.println("-reach includes reachability fact (for tcmc only)");
            //System.out.println("-enough includes enoughOperations pred");
            System.out.println("-c # is cmdnum to execute");
            System.out.println("-t is translateOnly");
            System.out.println("-r is resolveOnly");
            System.out.println("-e is echo file from internal parsed data");
            System.out.println("expects .dsh or .als file");
            System.out.println("if given a .als files, it ignores other options and runs all its commands");
            System.exit(0);
        }

        // simple roll-our-own argument parser
        // to avoid having to import an external package

        List<String> filelist = new ArrayList<>();

        // default values
        String method = "traces";
        Integer cmdnum = 0;
        Boolean translateOnly = false;
        Boolean printOnly = false;
        Boolean resolveOnly = false;

        for (int i=0; i<args.length;i++) {
            if (args[i].equals("-m")) {
                if (i+1 != args.length) {
                    method = args[i+1];
                    if (!(method.equals("traces") | method.equals("tcmc") | method.equals("electrum"))) {
                        System.err.println("-method must be traces, tcmc, or electrum");
                        System.exit(0);
                    }
                } else {
                   System.err.println("Method must be followed by traces, tcmc, or electrum");
                   System.exit(0); 
                }
                i++;
            } else if (args[i].equals("-c")) {
                if (i+1 != args.length) {
                    cmdnum = Integer.parseInt(args[i+1]);
                    if (cmdnum < 0) {
                        System.err.println("Command number must be greater than 1");
                        System.exit(0);
                    }
                } else {
                   System.err.println("-c must be followed by a number");
                   System.exit(0); 
                }
                i++;                   
            } else if (args[i].equals("-t")) {
                translateOnly = true;
            } else if (args[i].equals("-e")) {
                printOnly = true;
            } else if (args[i].equals("-r")) {
                resolveOnly = true;
            } /* else if (args[i].equals("-single")) {
                DashOptions.singleEventInput = true;
            } else if (args[i].equals("-reach")) {
                DashOptions.reachability = true;
            } else if (args[i].equals("-enough")) {
                DashOptions.enoughOperations = true;
            } */ else {
                // everything else is a file name
                filelist.add(args[i]);
            }
        }

        System.out.println("Alloy/Dash Analyzer: " + Version.getShortversion() + " built " + Version.buildDate());
        DashOptions.isTraces = (method.equals("traces"));
        DashOptions.isTcmc = (method.equals("tcmc"));
        DashOptions.isElectrum = (method.equals("electrum"));    

        for (String filename : filelist) {
            // add the .dsh extension if not included
            if (!filename.endsWith(".dsh") && !filename.endsWith(".als")) {
                int index = filename.lastIndexOf('.');
                if (index > 0) {
                    System.err.println("Expected a Dash file with 'dsh' or 'als' extension: "+filename);
                    break;
                } else {
                    filename = filename + ".dsh";
                }
            }

            Path f = Paths.get(filename);

            if (Files.notExists(f)) {
                System.err.println(filename + " : does not exist");
                return;
            }
            
            Path directory = f.toAbsolutePath().getParent();
            if (directory.toString() != null)
                DashOptions.dashModelLocation = directory.toString();

            
            System.out.println("Reading: " + filename );
            System.out.println("Method: " + method +"\n");
            A4Reporter rep = new A4Reporter();

            if (filename.endsWith(".als")) {
                try {
                    CompModule c = MainFunctions.parseAlloyFileAndResolveAll(filename, rep);
                    System.out.println("Parsed Alloy file");
                    // will raise an exception if problems
                    System.out.println("Resolved Alloy file");
                    executeCommands(c,cmdnum,rep);
                } catch (Exception e) {
                    DashUtilFcns.handleException(e);
                }
            } else {
                try {
                    DashModule d = MainFunctions.parseDashFile(filename, rep);
                    System.out.println("Parsed Dash file");
                    if (d == null) DashErrors.emptyFile(filename);
                    if (printOnly) {
                        System.out.println(d.toStringAlloy());
                    } else {
                        d = MainFunctions.resolveDash(d, rep);
                        System.out.println("Resolved Dash"); 
                        CompModule c = MainFunctions.translate(d, rep);
                        System.out.println("Translated Dash to Alloy"); 
                        // if problem exception would be raised 
                        if (translateOnly) {
                            String outfilename = filename.substring(0,filename.length()-4) + "-" + method + ".als";
                            File out = new File(outfilename);
                            if (!out.exists()) out.createNewFile();
                            System.out.println("Creating: " + outfilename);
                            FileWriter fw = new FileWriter(out.getAbsoluteFile());
                            BufferedWriter bw = new BufferedWriter(fw);
                            bw.write(d.toStringAlloy());
                            bw.close();
                        } else {
                            c = MainFunctions.resolveAlloy(c,rep);
                            System.out.println("Resolved Alloy");
                            if (!resolveOnly) {
                                executeCommands(c,cmdnum,rep);
                            }
                        }                   
                    }
                } catch (Exception e) {
                    DashUtilFcns.handleException(e);
                }
            }
        }
    }
}

