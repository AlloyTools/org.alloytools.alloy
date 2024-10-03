package ca.uwaterloo.watform.mainfunctions;

// drop this when removed print stmts here
import java.util.*;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.parser.CompUtil;

import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Options.SatSolver;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

import ca.uwaterloo.watform.core.DashSituation;
import ca.uwaterloo.watform.core.DashOptions;
import ca.uwaterloo.watform.core.DashErrors;
import ca.uwaterloo.watform.parser.DashUtil;
import ca.uwaterloo.watform.parser.DashModule;

import ca.uwaterloo.watform.predabstraction.PredicateAbstraction;


// no io in these!
// A4 reporter is not used in Dash stuff

public class MainFunctions {

    // all these function expect DashOptions to be set 

    public static DashModule parseDashFile(String filename, A4Reporter rep) {
        //DashOptions.isTraces = true;

        // some necessary initialization for two passes of parsing
        DashSituation.haveCountedBuffers = false;
        DashSituation.bufferElements = new ArrayList<String>();
        DashSituation.bufferNames = new ArrayList<String>();
        // first pass to collect buffers for open statements
        DashModule d = DashUtil.parseEverything_fromFileDash(rep, null, filename); 
        if (d == null) {
            DashErrors.emptyFile(filename);
        } else {
            DashSituation.haveCountedBuffers = true;
            // second pass, which will put in appropriate open statements for buffers
            d = DashUtil.parseEverything_fromFileDash(rep, null, filename); 
        }
        return d;     
    }
    public static DashModule resolveDash(DashModule d, A4Reporter rep) {
        if (d == null) {
           DashErrors.emptyModule();
        } else { 
           // done in place
           d.resolveAllDash(rep);
        }
        //d.debug();
        return d;
    }
    public static DashModule translate(DashModule d, A4Reporter rep) {
        if (d == null) {
            DashErrors.emptyModule();
        } else {
            // done in place 
            d.translate();
        }
        return d;
    }

    public static CompModule resolveAlloy(CompModule c, A4Reporter rep) {
        CompModule o = null;
        if (c == null) {
            DashErrors.emptyModule();
        } else {
            //System.out.println("here1");
            o = CompModule.resolveAll(rep,c);
            //System.out.println("here2");
        }
        return o;
    }

    // make our CLI also work for .als files
    public static CompModule parseAlloyFileAndResolveAll(String filename, A4Reporter rep) {
        CompModule c = CompUtil.parseEverything_fromFile(rep, null, filename);
        if (c == null) {
            DashErrors.emptyFile(filename);
        } 
        return c;
    }

    // for testing
    public static DashModule parseAndResolveDashFile(String filename, A4Reporter rep) {
        DashModule d = parseDashFile(filename,rep);
        return resolveDash(d,rep);
    }

    /*
    // only needed for testing
    public static void parseAndResolveAlloyFile(String filename, A4Reporter rep) {
        DashModule dash = null;

        DashOptions.isTraces = true;
        DashSituation.haveCountedBuffers = false;
        DashSituation.bufferElements = new ArrayList<String>();
        DashSituation.bufferNames = new ArrayList<String>();
        dash = DashUtil.parseEverything_fromFileDash(rep, null, filename); 
        if (dash == null) {
            System.err.println("Error in parsing");
            System.exit(1);
        } else {
            if (dash.hasRoot()) {
                System.err.println("Not a pure Alloy file");
                System.exit(1);
            } else {
                dash.resolveAllAlloy(rep); 
            }
        }
    }
    
    public static String alloyString(DashModule dash) {
        String s = null;
        if (dash != null) {
            s = dash.toString();
        }
        return s;
    }
    */
    /*
    public static DashModule translate(DashModule dash, A4Reporter rep) {

        DashOptions.isTraces = true;
        if (dash != null) {
            // translates in place
            dash.translate();
        }
        // Alloy wff check
        dash.resolveAllAlloy(rep == null ? A4Reporter.NOP : rep);
        //System.out.println(dash.toString());

        return dash;
    }

    */
   public static A4Solution executeCommand(Command cmd, CompModule alloy, A4Reporter rep, A4Options options) {
        // TODO this should be an option also
        options.solver = A4Options.SatSolver.SAT4J;
        A4Solution ans = TranslateAlloyToKodkod.execute_command(rep, alloy.getAllReachableSigs(), cmd, options); 
        return ans;
    }

    // returns a deep copy of DashModule object
    public static DashModule copyDash(DashModule d) {
        if(d == null){
            DashErrors.emptyModule();
            return d;
        } 

        DashModule dcopy = PredicateAbstraction.copyDashModule(d);
        return dcopy;
    }
}