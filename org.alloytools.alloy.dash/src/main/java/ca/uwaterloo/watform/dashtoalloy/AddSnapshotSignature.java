package ca.uwaterloo.watform.dashtoalloy;

import java.util.Collections;
import java.util.stream.Collectors;
import java.util.List;
import java.util.ArrayList;
import java.util.Arrays;

import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Expr;

import ca.uwaterloo.watform.core.DashOptions;
import static ca.uwaterloo.watform.core.DashStrings.*;
import ca.uwaterloo.watform.core.DashUtilFcns;
import ca.uwaterloo.watform.core.DashRef;

// shortens the code to import these statically
import static ca.uwaterloo.watform.core.DashFQN.*;
import static ca.uwaterloo.watform.alloyasthelper.ExprHelper.*;

import ca.uwaterloo.watform.alloyasthelper.DeclExt;
import ca.uwaterloo.watform.alloyasthelper.ExprToString;

import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.parser.CompModuleHelper;

import static ca.uwaterloo.watform.dashtoalloy.Common.*;

public class AddSnapshotSignature {

    public static void addSnapshotSignature(DashModule d){
        if (DashOptions.isElectrum) {
            // if Electrum add var sigs 
            // scopesUsed0, conf0, event0
            
            d.alloyString += d.addVarSigSimple(scopesUsedName+"0", createVar(stateLabelName));
            d.alloyString += d.addVarSigSimple(confName+"0", createVar(stateLabelName));
            if (d.hasEvents())
                d.alloyString += d.addVarSigSimple(eventsName+"0", createVar(allEventsName));
            List<ExprVar> cop;
            for (int i = 1; i <= d.getMaxDepthParams(); i++) {
                cop = new ArrayList<ExprVar> (Collections.nCopies(i+1,createVar(identifierName)));
                // scopesUsed 1, etc.
                d.alloyString += d.addVarSigSimple(
                    scopesUsedName+Integer.toString(i), 
                    DashUtilFcns.newListWith(cop, createVar(stateLabelName)));
                // conf 1, etc.
                d.alloyString += d.addVarSigSimple(
                    confName+Integer.toString(i), 
                    DashUtilFcns.newListWith(cop, createVar(stateLabelName)));
                // event 1, etc.
                if (d.hasEvents() & d.hasEventsAti(i))
                    d.alloyString += d.addVarSigSimple(
                        eventsName+Integer.toString(i), 
                        DashUtilFcns.newListWith(cop, createVar(allEventsName)));
            }
        
            // stable: one boolean;
            if (d.hasConcurrency()) {            
                d.alloyString += d.addVarSigSimple(stableName, createVar(boolName));
            }
            // add dynamic symbols (vars and buffers)
            /*
            for (DashDynSymbols v: getDynSymbols()) {
                List<String> prms = Collections.nCopies(IdentifiersName, v.getParams().size());
                addVarSigSimple(
                    v.getFullyQualName(), 
                    createArrowList(prms+v.createAlloyTyp()));
            }    
            */
        } else {
            // if traces/tcmc sig Snapshot {} with fields
            List<Decl> decls = new ArrayList<Decl>();

            // scopesUsed0, conf0, event0
            //if (d.transAtThisParamDepth(0))
                decls.add(DeclExt.newSetDeclExt(scopesUsedName+"0", stateLabelName));
            decls.add(DeclExt.newSetDeclExt(confName+"0", stateLabelName));
            if (d.hasEvents())
                decls.add(DeclExt.newSetDeclExt(eventsName+"0", allEventsName));
            List<String> cop;        
            for (int i = 1; i <= d.getMaxDepthParams(); i++) {
                cop = Collections.nCopies(i+1,identifierName);
                // scopesUsed 1, etc. 
                //if (d.transAtThisParamDepth(i)) 
                    decls.add(DeclExt.newSetDeclExt(
                        scopesUsedName+Integer.toString(i), 
                        createArrowStringList(DashUtilFcns.newListWith(cop, stateLabelName))));
                // conf 1, etc.
                decls.add(DeclExt.newSetDeclExt(
                    confName+Integer.toString(i), 
                    createArrowStringList(DashUtilFcns.newListWith(cop, stateLabelName))));
                // event 1, etc.
                if (d.hasEvents() && d.hasEventsAti(i))
                    decls.add(new DeclExt(
                        eventsName+Integer.toString(i), 
                    createArrowStringList(DashUtilFcns.newListWith(cop, allEventsName))));
            }
            // stable: one boolean;
            if (d.hasConcurrency()) {    
                decls.add(new DeclExt(stableName, createOne(createVar(boolName))));
            }
            // add dynamic symbols (vars and buffers)
            /*
            for (DashDynSymbols v: getDynSymbols()) {
                List<String> prms = Collections.nCopies(IdentifiersName, v.getParams().size());
                decls.add(createDecl(
                    v.getFullyQualName(), 
                    createArrowList(prms+v.createAlloyTyp())));
            }
            */

            d.alloyString += d.addSigWithDeclsSimple( snapshotName, decls);
        }
        d.alloyString += "\n";
    }
}