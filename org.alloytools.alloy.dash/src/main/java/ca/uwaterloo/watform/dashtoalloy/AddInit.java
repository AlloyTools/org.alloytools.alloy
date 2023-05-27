package ca.uwaterloo.watform.dashtoalloy;

import java.util.Collections;
import java.util.stream.Collectors;
import java.util.List;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.stream.IntStream;

import edu.mit.csail.sdg.ast.Decl;
//import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Expr;

import ca.uwaterloo.watform.core.DashOptions;
import ca.uwaterloo.watform.core.DashStrings;
import ca.uwaterloo.watform.core.DashUtilFcns;
import ca.uwaterloo.watform.core.DashErrors;
import ca.uwaterloo.watform.core.DashRef;

// shortens the code to import these statically
import static ca.uwaterloo.watform.core.DashFQN.*;
import static ca.uwaterloo.watform.alloyasthelper.ExprHelper.*;

//import ca.uwaterloo.watform.alloyasthelper.DeclExt;
//import ca.uwaterloo.watform.alloyasthelper.ExprToString;

import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.parser.CompModuleHelper;

import static ca.uwaterloo.watform.dashtoalloy.Common.*;

public class AddInit {

   // --------------------------------------------------------------------------------------
    /*
        TODO add here
        TODO add Electrum
    */        
    public static void addInit(DashModule d) {

        List<String> prs = d.getAllParamsInOrder();
        List<Expr> body = new ArrayList<Expr>();
        
        // forall i. confi = default entries
        List<DashRef> entered = d.initialEntered();
        if (entered.isEmpty()) DashErrors.noInitialEntered();
        for (int i=0;i <= d.getMaxDepthParams(); i++) {
            List<Expr> ent = DashRef.hasNumParams(entered,i).stream()
                .map(x -> translateDashRefToArrow(x))
                .collect(Collectors.toList());
            if (!ent.isEmpty()) body.add(createEquals(curConf(i),createUnionList(ent)));
            else body.add(createEquals(curConf(i), createNone()));
        }
        for (int i = 1; i <= d.getMaxDepthParams(); i++) {
            // scopesUsedi = none
            body.add(createEquals(
                curScopesUsed(i),
                createNoneArrow(i)));
            // no limits on initial set of events except that they must be environmental
            //s.events1 :> internalEvents = none -> none
            if (d.hasEventsAti(i))
                body.add(createEquals(
                    createRangeRes(curEvents(i), allInternalEventsVar()),
                    createNoneArrow(i)));
        }
        
        


        // even if these are empty we need this predicate to exist
        for (Expr i: d.getInits())
            // these may have the use of parameters in them
            body.add(translateExpr(i,d));

        // it was really tricky to get these types/lists right
        // so don't try to combine these steps

        Expr e;
        if (!body.isEmpty()) {
            if (!prs.isEmpty())
                e = createAll(
                        paramDecls(DashUtilFcns.listOfInt(0,prs.size()-1), prs),
                        createAndFromList(body));
            else e = createAndFromList(body);
            body = new ArrayList<Expr>();
            body.add(e);
        }
        if (d.hasConcurrency()) body.add(curStableTrue());
        // init is a reserved word in Electrum
        if (DashOptions.isElectrum) {
            d.alloyString += d.addPredSimple(DashStrings.initFactName, new ArrayList<Decl>(), body);
        } else {
            d.alloyString += d.addPredSimple(
                DashStrings.initFactName, 
                curParamsDecls(DashUtilFcns.listOfInt(0,prs.size()-1), prs),
                body);
        }
    }
}