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
import ca.uwaterloo.watform.core.DashStrings;
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

public class AddSpaceSignatures {


    // same for Electrum and other
    
    public static void addSpaceSignatures(DashModule d) {
        // abstract sig Statelabel {}
        if (!d.hasOnlyOneState()) {
            d.alloyString += d.addAbstractSigSimple(DashStrings.stateLabelName);
            d.alloyString += d.addAbstractExtendsSigSimple(d.getRootName(),DashStrings.stateLabelName);
        }
        if (d.hasConcurrency()) {
            d.alloyString += d.addAbstractSigSimple(DashStrings.scopeLabelName);
            d.alloyString += d.addOneExtendsSigSimple(d.getRootName()+DashStrings.scopeSuffix,DashStrings.scopeLabelName);
        }
        recurseCreateStateSpaceSigs(d, d.getRootName());
        d.alloyString += "\n";

 
        // abstract sig TransLabel {}
        d.alloyString += d.addAbstractSigSimple(DashStrings.transitionLabelName);
        //d.alloyString += d.addOneExtendsSigSimple(DashStrings.noTransName, DashStrings.transitionLabelName);
        // add all transitions as one sig extensions of TransLabel
        for (String t : d.getAllTransNames()) {
            d.alloyString += d.addOneExtendsSigSimple(translateFQN(t), DashStrings.transitionLabelName);
        }
        d.alloyString += "\n";

        // abstract sig Identifiers {} if this model has parametrized components
        // if not Electrum
        // o/w conf1, etc have to be fields in sig Identifiers
        // and this functionality is within AddSnapshotSignatures
        if (!DashOptions.isElectrum)
            if (d.getMaxDepthParams() != 0) {
                d.alloyString += d.addAbstractSigSimple(DashStrings.identifierName);
                for (String s: DashUtilFcns.listToSet(d.getAllParamsInOrder()))
                    d.alloyString += d.addExtendsSigSimple(s, DashStrings.identifierName);
                d.alloyString += "\n";
            }
        
        // events ----------------------
        if (d.hasEvents()) {
            d.alloyString += d.addAbstractSigSimple(DashStrings.allEventsName);
            if (d.hasInternalEvents()) {
                d.alloyString += d.addAbstractExtendsSigSimple(DashStrings.allInternalEventsName, DashStrings.allEventsName);
                    for (String e: d.getAllInternalEventNames()) {
                        d.alloyString += d.addOneExtendsSigSimple(translateFQN(e),DashStrings.allInternalEventsName);
                    }
            } 
            if (d.hasEnvironmentalEvents()){
                d.alloyString += d.addAbstractExtendsSigSimple( DashStrings.allEnvironmentalEventsName, DashStrings.allEventsName);
                for (String e: d.getAllEnvironmentalEventNames()) {
                    d.alloyString += d.addOneExtendsSigSimple(translateFQN(e),DashStrings.allEnvironmentalEventsName);
                }
            }
            d.alloyString += "\n";
        }

        // abstract sig BufIdx {} if this model has buffers
        // if not Electrum or if this buffer would be grouped under a parameter in Electrum declaration
        // o/w buffers have to be fields in sig BufIdx
        // and this functionality is within AddSnapshotSignatures        

        if (d.hasBuffers()) {
            // buffers with parameters
            // every buffer has a different index
            // so just one decl per sig
            List<String> allbfqns = d.getAllBufferNames();
            for (String b:allbfqns) {
                if (DashOptions.isElectrum) {
                    if (d.getVarBufferParams(b).size() != 0)
                        // because buffer is declared under param
                        // o/w declared with buffer index in Snapshot stuff
                        d.alloyString += d.addSigSimple(DashStrings.bufferIndexName + d.getBufferIndex(b));
                } else 
                    d.alloyString += d.addSigSimple(DashStrings.bufferIndexName + d.getBufferIndex(b));
            }
        } 

    }
    private static void recurseCreateStateSpaceSigs(DashModule d, String parent) {
        for (String child: d.getImmChildren(parent)) {
            //System.out.println(translateFQN(child)+" "+translateFQN(parent));
            // for scopes Used
            // Root node can be used for both conf and scopesUsed
            // but o/w concurrent nodes are abstract for conf
            // and one sigs for scopesUsed
            if (d.hasConcurrency() && d.isAnd(child))
                d.alloyString += d.addOneExtendsSigSimple(translateFQN(child)+DashStrings.scopeSuffix,DashStrings.scopeLabelName);
            // for conf
            if (!d.hasOnlyOneState()) {
                if (d.isLeaf(child)) d.alloyString += d.addOneExtendsSigSimple(translateFQN(child),translateFQN(parent));
                else {
                    //if (d.isAnd(parent)) 
                        //d.alloyString += d.addExtendsSigSimple(translateFQN(child), translateFQN(parent));
                    //else 
                    String x = d.addAbstractExtendsSigSimple(translateFQN(child), translateFQN(parent));
                    d.alloyString += x;
                    //System.out.println("HERE" + x);
                }
            }
            if (!d.isLeaf(child)) recurseCreateStateSpaceSigs(d,child);  
        }  
    }
}