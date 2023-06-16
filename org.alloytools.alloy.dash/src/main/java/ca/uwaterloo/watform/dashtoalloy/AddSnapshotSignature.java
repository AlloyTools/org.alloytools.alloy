package ca.uwaterloo.watform.dashtoalloy;

import java.util.Collections;
import java.util.stream.Collectors;
import java.util.List;
import java.util.ArrayList;
import java.util.Arrays;

import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.ExprUnary;
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
            List<Decl> decls;

            d.alloyString += d.addVarSigSimple(scopesUsedName+"0", createVar(stateLabelName));
            d.alloyString += d.addVarSigSimple(confName+"0", createVar(stateLabelName));
            if (d.hasEvents())
                d.alloyString += d.addVarSigSimple(eventsName+"0", createVar(allEventsName));

            // sig Identifiers {
            //        conf1: StateLabel,
            //        scopesUsed1: StateLabel,
            //        events1: AllEvent,
            //        conf2: Identifiers -> StateLabel,
            //        scopesUsed2: Identifers -> StateLabel,
            //        etc
            // }
            if (d.getMaxDepthParams() != 0) {
                List<Expr> cop;
                decls = new ArrayList<Decl>();
                for (int i = 1; i <= d.getMaxDepthParams(); i++) {
                    cop = new ArrayList<Expr> (Collections.nCopies(i-1,createVar(identifierName)));
                    // conf 1, etc.
                    decls.add(
                        DeclExt.newVarDeclExt(
                            confName+Integer.toString(i), 
                            createArrowExprList(DashUtilFcns.newListWith(cop, createSet(createVar(stateLabelName))))));
                    // scopesUsed 1, etc.
                    decls.add(
                        DeclExt.newVarDeclExt(
                            scopesUsedName+Integer.toString(i), 
                            createArrowExprList(DashUtilFcns.newListWith(cop, createSet(createVar(stateLabelName))))));
                    if (d.hasEvents() & d.hasEventsAti(i))
                        // events 1, etc.
                        decls.add(
                            DeclExt.newVarDeclExt(
                                eventsName+Integer.toString(i), 
                                createArrowExprList(DashUtilFcns.newListWith(cop, createSet(createVar(allEventsName))))));
                }
                d.alloyString += d.addSigWithDeclsSimple(identifierName, decls);
            }
        
            // stable: one boolean;
            if (d.hasConcurrency()) {            
                d.alloyString += d.addVarSigSimple(stableName, createVar(boolName));
            }
            // add vars and parameter sets --------------------------------------

            
            List<String> allvfqns = d.getAllVarNames();
            List<String> allbfqns = d.getAllBufferNames();

            // vfqns with no params and simple type
            // becomes var sig vfqn in var {}
            // no buffers in this case
            // this is tricky if one/lone/set modifiers on type ***
            List<String> allvfqnsNoParamsSimpleTyp = allvfqns.stream()
                .filter(i -> d.getVarBufferParams(i).size() == 0 && !isWeirdOne(i,d))
                .collect(Collectors.toList());
            for (String v: allvfqnsNoParamsSimpleTyp) {
                
                Expr typ = d.getVarType(v);
                //System.out.println(typ.getClass());
                //System.out.println(((ExprUnary) typ).op);
                if (isExprVar(typ)) {
                    d.alloyString += d.addVarSigSimple(translateFQN(v), ((ExprVar) translateExpr(typ,d,true)) );
                } else if (isExprSet(typ) && isExprVar(getSub(typ))) {
                    d.alloyString += d.addVarSigSimple(translateFQN(v), ((ExprVar)translateExpr(getSub(typ),d,true)) );
                } else if (isExprLone(typ) && isExprVar(getSub(typ))) {
                    d.alloyString += d.addVarLoneSigSimple(translateFQN(v), ((ExprVar)translateExpr(getSub(typ),d,true)) );
                } else if (isExprOne(typ) && isExprVar(getSub(typ))) {
                    d.alloyString += d.addVarOneSigSimple(translateFQN(v), ((ExprVar) translateExpr(getSub(typ),d,true)) );
                } else {
                    TranslationToAlloyErrors.Unsupported(typ);
                }
            }
            
            // vfqns with no params and non-simple var types (weird ones)
            // becomes sig A { var vfqn: B }
            // but A has already been declared somewhere by the user
            // and we can't easily add a field to an existing signature in
            // Alloy module, so instead add one atom to model 
            // one sig Variables {
            //     v1: typ1
            // }
            // and have to deal with this case in translation to Alloy
            // no buffers in this case because they can be grouped with index
            List<String> allvfqnsNoParamsArrowTyp = allvfqns.stream()
                .filter(i -> Common.isWeirdOne(i,d))
                .collect(Collectors.toList());
            if (!allvfqnsNoParamsArrowTyp.isEmpty()) {
                decls = new ArrayList<Decl>();
                for (String v: allvfqnsNoParamsArrowTyp) 
                    decls.add(DeclExt.newVarDeclExt(translateFQN(v), translateExpr(d.getVarType(v),d, true)));
                d.alloyString += d.addOneSigWithDeclsSimple(DashStrings.variablesName, decls);
            }

            // vfqns with parameters P1, P2, P3
            // sig P1 {
            //      var v1: P2 -> P3 ->  typ1
            //      var buf: P2 -> P3 -> bufindex -> eltype
            // } 
            // it is enough to look at state parameters to get all parameters
            List<String> allvfqnsWithThisFirstParam;
            List<String> allbfqnsWithThisFirstParam;
            List<Expr> plist;

            for (String prm: DashUtilFcns.listToSet(d.getAllParamsInOrder())) {

                // variables with parameters grouped with parameter
                allvfqnsWithThisFirstParam = allvfqns.stream()
                    // must be at least one parameter
                    .filter(i -> d.getVarBufferParams(i).size() != 0 && d.getVarBufferParams(i).get(0).equals(prm))
                    .collect(Collectors.toList());
                // construct decls -- might be none but still have to 
                // create sig for this parameter
                decls = new ArrayList<Decl>();
                for (String v: allvfqnsWithThisFirstParam) {
                    if (d.getVarBufferParams(v).size() == 1) {
                        decls.add(DeclExt.newVarDeclExt(translateFQN(v), translateExpr(d.getVarType(v),d, true)));
                    } else {
                        plist = createVarList(d.getVarBufferParams(v).subList(1, d.getVarBufferParams(v).size()-1));
                        plist.add(translateExpr(d.getVarType(v),d, true));
                        decls.add(DeclExt.newVarDeclExt(translateFQN(v),createArrowExprList(plist)));
                    }
                }
                // buffers with parameters grouped with parameter
                allbfqnsWithThisFirstParam = allbfqns.stream()
                    // must be at least one parameter
                    .filter(i -> d.getVarBufferParams(i).size() != 0 && d.getVarBufferParams(i).get(0).equals(prm))
                    .collect(Collectors.toList());
                // construct decls -- might be none but still have to 
                // create sig for this parameter
                for (String b: allbfqnsWithThisFirstParam) {
                    if (d.getVarBufferParams(b).size() != 1)
                        plist = createVarList(d.getVarBufferParams(b).subList(1, d.getVarBufferParams(b).size()-1));
                    else
                        plist = new ArrayList<Expr>();
                    plist.add(bufferIndexVar(d.getBufferIndex(b)));
                    plist.add(createVar(d.getBufferElement(b)));
                    decls.add(DeclExt.newVarDeclExt(translateFQN(b),createArrowExprList(plist)));
                }
                d.alloyString += d.addSigExtendsWithDeclsSimple(prm, identifierName, decls);

            }

            // buffers with no parameters
            // grouped in buffer index introduction
            // every buffer has a different index
            // so just one decl per sig
            List<String> allbfqnsWithNoParams = allbfqns.stream()
                // must be at least one parameter
                .filter(i -> d.getVarBufferParams(i).size() == 0 )
                .collect(Collectors.toList());     
            for (String b: allbfqnsWithNoParams) {
                decls = new ArrayList<Decl>();
                decls.add(DeclExt.newVarDeclExt(
                            translateFQN(b),
                            createVar(d.getBufferElement(b))));
                d.alloyString += d.addSigWithDeclsSimple(
                    bufferIndexName + d.getBufferIndex(b),
                    decls);
            }           
            
        } else {
            // if traces/tcmc sig Snapshot {} with fields
            List<Decl> decls = new ArrayList<Decl>();

            // scopesUsed0, conf0, event0
            //if (d.transAtThisParamDepth(0))
            //TODO: if no concurrency, don't need scopesUsed !!
            decls.add(DeclExt.newSetDeclExt(scopesUsedName+"0", stateLabelName));
            decls.add(DeclExt.newSetDeclExt(confName+"0", stateLabelName));
            if (d.hasEvents())
                decls.add(DeclExt.newSetDeclExt(eventsName+"0", allEventsName));
            List<String> cop;        
            for (int i = 1; i <= d.getMaxDepthParams(); i++) {
                cop = Collections.nCopies(i,identifierName);
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
                typlist = createVarList(d.getVarBufferParams(vfqn)); // could be empty
                typlist.add(translateExpr(d.getVarType(vfqn),d, true));
                //System.out.println(d.getVarType(vfqn));
                //System.out.println(translateExpr(d.getVarType(vfqn),d, true));
                if (typlist.size() > 1 ) {
                    decls.add((Decl) new DeclExt(
                        translateFQN(vfqn), 
                        createArrowExprList(typlist)));
                    //System.out.println(decls);
                }
                else {
                    decls.add((Decl) new DeclExt(
                        translateFQN(vfqn), 
                        typlist.get(0))); 
                    //System.out.println(decls);           
                }
            } 
            // add buffers
            for (String bfqn: d.getAllBufferNames()) {       
                typlist = createVarList(d.getVarBufferParams(bfqn)); // could be empty
                typlist.add(bufferIndexVar(d.getBufferIndex(bfqn)));
                typlist.add(createVar(d.getBufferElement(bfqn)));
                if (typlist.size() > 1 )
                    decls.add((Decl) new DeclExt(
                        translateFQN(bfqn), 
                        createArrowExprList(typlist)));
                else 
                    decls.add((Decl) new DeclExt(
                        translateFQN(bfqn), 
                        typlist.get(0)));            
            }             
            d.alloyString += d.addSigWithDeclsSimple( snapshotName, decls);
        }
        d.alloyString += "\n";
    }
}