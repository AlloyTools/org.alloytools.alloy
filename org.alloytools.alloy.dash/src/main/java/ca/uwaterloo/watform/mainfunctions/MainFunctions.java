package ca.uwaterloo.watform.mainfunctions;

// drop this when removed print stmts here
import java.util.*;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.parser.CompModule;

import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Options.SatSolver;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

import ca.uwaterloo.watform.core.DashSituation;
import ca.uwaterloo.watform.core.DashOptions;
import ca.uwaterloo.watform.parser.DashUtil;
import ca.uwaterloo.watform.parser.DashModule;


// no io in these!


public class MainFunctions {

    // both these function expect DashOptions to be set 

    public static DashModule parseFile(String filename, A4Reporter rep) {
        DashModule dash = null;
        try {
            DashOptions.isTraces = true;
            DashSituation.haveCountedBuffers = false;
            DashSituation.bufferElements = new ArrayList<String>();
            DashSituation.bufferNames = new ArrayList<String>();
            dash = DashUtil.parseEverything_fromFileDash(rep, null, filename); 
            if (dash == null) {
                System.err.println("Empty Alloy file");
            } else {
                DashSituation.haveCountedBuffers = true;
                dash = DashUtil.parseEverything_fromFileDash(rep, null, filename); 
                //System.out.println(filename + " parsed successfully.");
                // well-formedness checks
                dash.resolveAllDash(rep); 
                //System.out.println(dash.toString());
            }
        } catch (Exception e) {
            e.printStackTrace(System.err);
            System.err.println(e);
            System.exit(1);
        }
        return dash;     
    }
    public static String dumpString(DashModule dash) {
       String s = null;
       try {
            if (dash != null) {
                s = dash.toString();
            }
        } catch (Exception e) {
            System.err.println(e);
        }     
        return s;
    }

    public static DashModule translate(DashModule dash, A4Reporter rep) {
        try {
            DashOptions.isTraces = true;
            if (dash != null) {
                // translates in place
                dash.translate();
            }
            // Alloy wff check
            dash.resolveAllAlloy(rep == null ? A4Reporter.NOP : rep);
            System.out.println(dash.toString());
        } catch (Exception e) {
            e.printStackTrace(System.err);
            System.err.println(e);
            System.exit(1);
        }
        return dash;
    }

   public static A4Solution executeCommand(Command cmd, CompModule alloy, A4Reporter rep, A4Options options) {


        //TODO this should be an option also
        options.solver = A4Options.SatSolver.SAT4J;

        A4Solution ans = TranslateAlloyToKodkod.execute_command(rep, alloy.getAllReachableSigs(), cmd, options); 
        return ans;

    }



}