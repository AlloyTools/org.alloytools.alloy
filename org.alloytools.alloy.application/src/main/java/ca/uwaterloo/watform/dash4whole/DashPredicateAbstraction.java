/*
 * CLI for doing predicate abstraction. For now, it takes a .dsh file as input, parses and resolves it, and uses the populated DS to make a copy.
 */
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

public class DashPredicateAbstraction {
    public static void main(String args[]) throws Exception { 

        if(args.length == 0) {
            System.out.println("Argument missing: filename");
            System.exit(0);
        }
        else if(args.length > 1){
            System.out.println("Expected 1 Argument, Received" + args.length + "Arguments");
            System.exit(0);
        }

        String inputFilename = args[0]; 

        // default values
        String method = "traces";
        Integer cmdnum = 0;
        Boolean translateOnly = false;
        Boolean printOnly = false;
        Boolean resolveOnly = false;

        // for (int i=0; i<args.length;i++) {
        //     if (args[i].equals("-m")) {
        //         if (i+1 != args.length) {
        //             method = args[i+1];
        //             if (!(method.equals("traces") | method.equals("tcmc") | method.equals("electrum"))) {
        //                 System.err.println("-method must be traces, tcmc, or electrum");
        //                 System.exit(0);
        //             }
        //         } else {
        //            System.err.println("Method must be followed by traces, tcmc, or electrum");
        //            System.exit(0); 
        //         }
        //         i++;
        //     } else if (args[i].equals("-c")) {
        //         if (i+1 != args.length) {
        //             cmdnum = Integer.parseInt(args[i+1]);
        //             if (cmdnum < 0) {
        //                 System.err.println("Command number must be greater than 1");
        //                 System.exit(0);
        //             }
        //         } else {
        //            System.err.println("-c must be followed by a number");
        //            System.exit(0); 
        //         }
        //         i++;                   
        //     } else if (args[i].equals("-t")) {
        //         translateOnly = true;
        //     } else if (args[i].equals("-e")) {
        //         printOnly = true;
        //     } else if (args[i].equals("-r")) {
        //         resolveOnly = true;
        //     } /* else if (args[i].equals("-single")) {
        //         DashOptions.singleEventInput = true;
        //     } else if (args[i].equals("-reach")) {
        //         DashOptions.reachability = true;
        //     } else if (args[i].equals("-enough")) {
        //         DashOptions.enoughOperations = true;
        //     } */ else {
        //         // everything else is a file name
        //         filelist.add(args[i]);
        //     }
        // }

        System.out.println("Alloy/Dash Analyzer: " + Version.getShortversion() + " built " + Version.buildDate());
        DashOptions.isTraces = (method.equals("traces"));
        DashOptions.isTcmc = (method.equals("tcmc"));
        DashOptions.isElectrum = (method.equals("electrum"));    

        if(!inputFilename.endsWith(".dsh")){
            int index = inputFilename.lastIndexOf('.');
            if (index > 0) {
                System.err.println("Expected a Dash file with 'dsh' extension: " + inputFilename);
                System.exit(-1);
            } else {
                inputFilename = inputFilename + ".dsh";
            }
        }

        Path f = Paths.get(inputFilename);

        if (Files.notExists(f)) {
            System.err.println(inputFilename + " : does not exist");
            return;
        }
            
        Path directory = f.toAbsolutePath().getParent();
        if (directory.toString() != null)
            DashOptions.dashModelLocation = directory.toString();

            
        System.out.println("Reading: " + inputFilename );
            
        A4Reporter rep = new A4Reporter();

        try {
                DashModule d = MainFunctions.parseDashFile(inputFilename, rep);
                System.out.println("Parsed Dash file");
                if (d == null) 
                    DashErrors.emptyFile(inputFilename);
                
                CompModule c = MainFunctions.translate(d, rep);
                
                    //     System.out.println("Translated Dash to Alloy"); 
                    //     System.out.println("Method: " + method +"\n");
                    //     // if problem exception would be raised 
                    //     if (translateOnly) {
                    //         String outfilename = filename.substring(0,filename.length()-4) + "-" + method + ".als";
                    //         File out = new File(outfilename);
                    //         if (!out.exists()) out.createNewFile();
                    //         System.out.println("Creating: " + outfilename);
                    //         FileWriter fw = new FileWriter(out.getAbsoluteFile());
                    //         BufferedWriter bw = new BufferedWriter(fw);
                    //         bw.write(d.toStringAlloy());
                    //         bw.close();
                    //     } else {
                    //         c = MainFunctions.resolveAlloy(c,rep);
                    //         System.out.println("Resolved Alloy");
                    //         if (!resolveOnly) {
                    //             executeCommands(c,cmdnum,rep);
                    //         }
                    //     }                   
                    // }
                        
                d = MainFunctions.resolveDash(d, rep);
                System.out.println("Resolved Dash"); 

                DashModule dcopy = MainFunctions.copyDash(d);
                System.out.println("Deep copy of Dash model created");
                    
                } catch (Exception e) {
                    DashUtilFcns.handleException(e);
                }
    }
}
