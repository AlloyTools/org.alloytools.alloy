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
import ca.uwaterloo.watform.core.DashStrings;

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
            // add vars and parameter sets --------------------------------------

            List<Decl> decls;
            List<String> allvfqns = d.getAllVarNames();

            // vfqns with no params and simple type
            // becomes var sig vfqn in var {}
            List<String> allvfqnsNoParamsSimpleTyp = allvfqns.stream()
                .filter(i -> d.getVarParams(i).size() == 0 && isExprVar(d.getVarType(i)))
                .collect(Collectors.toList());
            for (String v: allvfqnsNoParamsSimpleTyp) 
                d.alloyString += d.addVarSigSimple(translateFQN(v), ((ExprVar) d.getVarType(v)) );
            
            // vfqns with no params and arrow type (A -> B)
            // becomes sig A { var vfqn: B }
            // but A has already been declared somewhere by the user
            // and we can't easily add a field to an existing signature in
            // Alloy module, so instead add one atom to model 
            // one sig Variables {
            //     v1: typ1
            // }
            // and have to deal with this case in translation to Alloy
            List<String> allvfqnsNoParamsArrowTyp = allvfqns.stream()
                .filter(i -> d.getVarParams(i).size() == 0 && isExprArrow(d.getVarType(i)))
                .collect(Collectors.toList());
            if (!allvfqnsNoParamsArrowTyp.isEmpty()) {
                decls = new ArrayList<Decl>();
                for (String v: allvfqnsNoParamsArrowTyp) 
                    decls.add(DeclExt.newVarDeclExt(translateFQN(v), d.getVarType(v)));
                d.alloyString += d.addOneSigWithDeclsSimple(DashStrings.variablesName, decls);
            }

            // vfqns with parameters P1, P2, P3
            // sig P1 {
            //      var v1: P2 -> P3 ->  typ1
            // } 
            // it is enough to look at state parameters to get all parameters
            List<String> allvfqnsWithThisFirstParam;
            
            for (String prm: d.getAllParams()) {
                allvfqnsWithThisFirstParam = allvfqns.stream()
                    // must be at least one parameter
                    .filter(i -> d.getVarParams(i).size() != 0 && d.getVarParams(i).get(0).equals(prm))
                    .collect(Collectors.toList());
                // construct decls -- might be none but still have to 
                // create sig for this parameter
                decls = new ArrayList<Decl>();
                for (String v: allvfqnsWithThisFirstParam) {
                    if (d.getVarParams(v).size() == 1) {
                        decls.add(new DeclExt(v, d.getVarType(v)));
                    } else {
                        List<Expr> plist = createVarList(d.getVarParams(v).subList(1, d.getVarParams(v).size()-1));
                        plist.add(d.getVarType(v));
                        decls.add(DeclExt.newVarDeclExt(translateFQN(v),createArrowExprList(plist)));
                    }
                }
                d.alloyString += d.addSigWithDeclsSimple(prm, decls);
            }
            
            // add buffers
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
                    decls.add((Decl) new DeclExt(
                        scopesUsedName+Integer.toString(i), 
                        createArrowStringList(DashUtilFcns.newListWith(cop, stateLabelName))));
                // conf 1, etc.
                decls.add((Decl) new DeclExt(
                    confName+Integer.toString(i), 
                    createArrowStringList(DashUtilFcns.newListWith(cop, stateLabelName))));
                // event 1, etc.
                if (d.hasEvents() && d.hasEventsAti(i))
                    decls.add((Decl) new DeclExt(
                        eventsName+Integer.toString(i), 
                    createArrowStringList(DashUtilFcns.newListWith(cop, allEventsName))));
            }
            // stable: one boolean;
            if (d.hasConcurrency()) {    
                decls.add(new DeclExt(stableName, createOne(createVar(boolName))));
            }
            // add vars
            List<Expr> typlist;
            for (String vfqn: d.getAllVarNames()) {
                typlist = createVarList(d.getVarParams(vfqn)); // could be empty
                typlist.add(d.getVarType(vfqn));
                if (typlist.size() > 1 )
                    decls.add((Decl) new DeclExt(
                        translateFQN(vfqn), 
                        createArrowExprList(typlist)));
                else 
                    decls.add((Decl) new DeclExt(
                        translateFQN(vfqn), 
                        typlist.get(0)));            
            } 
            // add buffers
            d.alloyString += d.addSigWithDeclsSimple( snapshotName, decls);
        }
        d.alloyString += "\n";
    }
}