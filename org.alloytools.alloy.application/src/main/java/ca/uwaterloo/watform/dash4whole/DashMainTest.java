/*
    The purpose of this code is to help 
    with debugging
*/

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
import ca.uwaterloo.watform.core.DashFQN;
import ca.uwaterloo.watform.parser.DashUtil;
import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.mainfunctions.MainFunctions;




public class DashMainTest {




    public static void main(String args[]) { 
 
        System.out.println("Starting DashMainTest");
        A4Reporter rep = new A4Reporter();
        if(args.length != 0) {
            // first arg is filename
            String fname = args[0];
            DashModule d = 
                MainFunctions.parseAndResolveDashFile(fname,rep);
            if (args.length == 2) {
                // transition name
                d.debug(args[1]);
            } else d.debug();
        }
        /*
        DashModule d = 
            MainFunctions.parseAndResolveDashFile(
                "/Users/nday/UW/github/org.alloytools.alloy/org.alloytools.alloy.dash/src/test/resources/wfffail/noTrans1.dsh",rep);
        */
        //List<String> p = DashFQN.allPrefixes("A/B/C");
        //List<String> k = (new String[]{"A", "A/B", "A/B/C"} ;
        //System.out.println("all prefixes: " + p);
        //assert(p.equals());
        System.out.println("Finish DashMainTest");
    }
}

