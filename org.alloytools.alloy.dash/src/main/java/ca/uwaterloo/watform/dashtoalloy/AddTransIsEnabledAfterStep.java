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

public class AddTransIsEnabledAfterStep {
    // ---------------------------------------------------
    /*
    // this is considering all instances of t1s (thus, the existential quantification)
    pred t1_enabledAfterStep[
            s:Snapshot,s':Snapshot,  
            pParam0: Param0, ...
            t:TransitionLabel, // parameters don't matter for orthogonality
            ge:EventLabel ] 
    {   // b/c below is exists params, the params don't matter
        src_state_t1 in s'.confi // where i is depth of src_state, 
        guard_cond_t1[s'] // may depend on params
        (s.stable = True) =>
            no t1.notOrthogonal & t 
            for all of t1's triggering events and forall n
                (if trig_ev_t1 is internal, line below is false)
                trig_ev_t1  in (chop0(s.event0,EnvEvents) + chop1(s.event1,EnvEvents) + chop2(s.event2,EnvEvents) ... + ge)
        else {
            no t1.notOrthogonal & (t + s.scopesUsed0 + s.scopesUsed1.TransLabel + s.scopesUsed2.TransLabel + s.scopesUsed3.TransLabel ...)
            for all of t1's triggering events and forall n
                trig_ev_t1  in (s.event0.EventLabel + s.event1.EventLabel + s.event2.EventLabel ... + ge)     
        }
    }
    */
    public static void  addTransIsEnabledAfterStep(DashModule d, String tfqn) {

        //TODO fix this one

        String tout = translateFQN(tfqn);
        List<String> prs = d.getTransParams(tfqn); 
        List<Decl> decls = new ArrayList<Decl>();
        List<Expr> body = new ArrayList<Expr>();

        if (!DashOptions.isElectrum) {
            decls.addAll(curNextDecls());
        }
        for (int i=0; i<= d.getMaxDepthParams(); i++) {
            decls.add(scopesUsedDecl(i));
            if (d.hasEventsAti(i)) {
                decls.add(eventsDecl(i));
            }
        }    


        // p3 -> p2 -> p1 -> src in s'.confVar(i)
        // src does not have to be a basic state  
        body.add(createIn(d.getTransSrc(tfqn).toAlloy(),nextConf(prs.size())));

        // guard condition is true is '
        // TOD
        d.alloyString += d.addPredSimple(tout+DashStrings.enabledAfterStepName,decls,body);
        /*
        ArrayList<Expr> o = new ArrayList<Expr>();

        
        // src does not have to be a basic state 
        Expr src = createVar(dash.getTransSrc(t));
        ArrayList<Expr> psList = createVars(prs); 
        List<String> trig_ev = dash.transTable.get(t).getWhen();
        List<String> int_trig_ev = trig_ev.stream().filter(ev -> ev.isInternal()).collect(Collectors.toList());

        // p3 -> p2 -> p1 -> src in s'.confVar(i)    
        o.add(createIn(createArrowList(createVars(prs).add(src)),nextConf(prs.size())));

        // guard_cond_t1 [s'] 
        // final parameter (usually s') should not be used in precondition
        o.add(dash.getTransGuard(t).convertToAlloy(dash.symbolTable, nextVar(), null, prs));


        // no t1.notOrthogonal & (t + s.scopesUsed + s.scopesUsed1 |> TransitionLabel + scopesUsed2 |> TransitionLabel + ...)  
        Expr elseExpr = createNo(
            createAnd(
                createNonOrthogonalExpr(t),createPlus(createVar(t), 
                createChoppedGroup(prs.size(),DashStrings.scopesUsedName,DashStrings.transitionLabelName))));
        elseExpr = createAnd(
            elseExpr,
            createIn(
                createPlusList(createVarList(trig_ev)),
                createPlus(
                    // chop(s.event0,EventLabel + chop(s.event1,EventLabel) + chop(s.event2,EventLabel) 
                    createChoppedGroup(prs.size(),DashStrings.eventName,DashStrings.eventLabelName),
                    ge)));

        if (int_trig_ev == null) {
            // no t1.notOrthogonal & t 
            Expr ifExpr = createNo(createAnd(createNonOrthogonalExpr(t),createVar(t)));
            ifExpr = createAnd(
                ifExpr,
                createIn(
                    createPlusList(createVarList(trig_ev)),
                    // chop(s.event0,EnvEvents) + chop1(s.event1,EnvEvents) + chop2(s.event2,EnvEvents)
                    createPlus(createChoppedGroup(prs.size(),DashStrings.eventName,DashStrings.environmentEventName),ge)))
            body.add(createITE(sStableTrue(),ifExpr,elseExpr));
        } else {
            body.add(createITE(sStableTrue(),createFalse(),elseExpr));
        }
        */
        /*
        List<Decl> decls = curNextParamsDecls(prs);
        decls.add((Decl) new DeclExt(DashStrings.tName, DashStrings.transitionLabelName));
        if (d.hasEvents())
            decls.add((Decl) DeclExt.newSetDeclExt(DashStrings.geName, DashStrings.eventLabelName));
        // tmp

        d.alloyString += "\n";
        */
    }


}