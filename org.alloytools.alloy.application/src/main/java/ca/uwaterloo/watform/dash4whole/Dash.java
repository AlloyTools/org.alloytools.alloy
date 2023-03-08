package ca.uwaterloo.watform.dash4whole;

import java.util.*;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.Files;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4viz.VizGUI;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

import ca.uwaterloo.watform.core.DashOptions;
import ca.uwaterloo.watform.parser.DashUtil;
import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.mainfunctions.MainFunctions;




public class Dash {

   @SuppressWarnings("resource" )

   public static void main(String args[]) throws Exception { 

        if(args.length == 0) {
            System.out.println("Arguments: (-m traces|tcmc|electrum) (-c #) (-p) (-t) filename(s); -c is cmdnum; -t is translateOnly");
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
            } else if (args[i].equals("-p")) {
                printOnly = true;
            } else {
                // everything else is a file name
                filelist.add(args[i]);
            }
        }

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

            //Parse+typecheck the model
            //System.out.println("Reading: " + filename );

            A4Reporter rep = new A4Reporter();
            CompModule alloymodule = null;
            DashModule d = MainFunctions.parseFile(filename.toString(), rep);
            if (printOnly) {  
                if (d != null) {
                    String o = MainFunctions.dumpString(d);
                    System.out.println(o);
                    // System.out.println("File parsed successfully.");
                }
            } else {
                try {
                    alloymodule = MainFunctions.translateToAlloy(d, rep);
                } catch (Exception e) {
                    System.err.println(e);
                    System.exit(1);
                }
                if (alloymodule == null) {
                    System.err.println("Something went wrong");
                    System.exit(1);
                }
                if (translateOnly) {
                    try {
                        // have to fix output name
                        String outfilename = filename.substring(0,filename.length()-4) + "-" + method + ".als";
                        File out = new File(outfilename);
                        if (!out.exists()) {
                            out.createNewFile();
                        }
                        System.out.println("Creating: " + outfilename);
                        // NAD tmp
                        //String content = new DashModuleToString(true).getString(alloymodule);
                        //FileWriter fw = new FileWriter(out.getAbsoluteFile());
                        //BufferedWriter bw = new BufferedWriter(fw);
                        //bw.write(content);
                        //bw.close();
                    } catch(Exception e){
                        System.err.println(e);
                    }
                } else {
                    // execute command(s)

                    // Choose some default options for how you want to execute the commands
                    A4Options options = new A4Options();

                    List<Command> commands = alloymodule.getAllCommands();
                    // this is an annoying way to convert a list to an array
                    Integer i = 1;
                    for (Command cmd : commands) { 
                        if (i == cmdnum | cmdnum == 0) {
                            System.out.println("Executing command: " + cmd);
                            A4Solution ans = MainFunctions.executeCommand(cmd,alloymodule,rep, options);
                            if (ans.satisfiable()) {
                                System.out.println("Result: SAT");
                            } else {
                                System.out.println("Result: UNSAT");
                            }
                        }
                        i++;
                    }
                    if (cmdnum >= i) {
                        System.err.println("Command number: " + cmdnum + " does not exist in file");
                    }
                }
            }
        }
    }
}

