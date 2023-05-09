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
        d.alloyString += d.addAbstractSigSimple(DashStrings.stateLabelName);
        // Root
        //if (d.hasConcurrency() || d.getImmChildren(d.getRootName()).isEmpty())
            d.alloyString += d.addExtendsSigSimple(d.getRootName(),DashStrings.stateLabelName);
        //else 
            //d.alloyString += d.addAbstractExtendsSigSimple(d.getRootName(),DashStrings.stateLabelName);
        //System.out.println(d.getRootName());
        recurseCreateStateSpaceSigs(d, d.getRootName());
        d.alloyString += "\n";

        // we don't need transition names anymore (rather we use scopes)
        // abstract sig TransLabel {}
        // d.alloyString += d.addAbstractSigSimple(DashStrings.transitionLabelName);
        // add all transitions as one sig extensions of TransLabel
        //for (String t : d.getTransNames()) {
            //d.alloyString += d.addOneExtendsSigSimple(translateFQN(t), DashStrings.transitionLabelName);
        //}
        //d.alloyString += "\n";

        // abstract sig Identifiers {} if this model has parametrized components
        // if not Electrum
        // o/w conf1, etc have to be fields in sig Identifiers
        // and this functionality is within AddSnapshotSignatures
        if (!DashOptions.isElectrum)
            if (d.getMaxDepthParams() != 0) {
                d.alloyString += d.addAbstractSigSimple(DashStrings.identifierName);
                for (String s: d.getAllParams())
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
        // if not Electrum
        // o/w buffers have to be fields in sig BufIdx
        // and this functionality is within AddSnapshotSignatures        
        if (!DashOptions.isElectrum && d.hasBuffers()) {
            for (int i: d.getBufferIndices()) {
                d.alloyString += d.addSigSimple(DashStrings.bufferIndexName + i);
            }
        } 

    }
    private static void recurseCreateStateSpaceSigs(DashModule d, String parent) {
        for (String child: d.getImmChildren(parent)) {
            //System.out.println(translateFQN(child)+" "+translateFQN(parent));
            if (d.isLeaf(child) || d.isAnd(child)) d.alloyString += d.addOneExtendsSigSimple(translateFQN(child),translateFQN(parent));
            else 
                //if (d.isAnd(parent)) 
                    //d.alloyString += d.addExtendsSigSimple(translateFQN(child), translateFQN(parent));
                //else 
                d.alloyString += d.addAbstractExtendsSigSimple(translateFQN(child), translateFQN(parent));
            if (!d.isLeaf(child)) recurseCreateStateSpaceSigs(d,child);  
        }  
    }
}