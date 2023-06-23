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
            pParam0: Param0, 
            ...
            scopes0: StateLabel,
            scopes1: Identifiers -> StateLabel,
            ...
            genEvents0:EventLabel,
            genEvents1: Identifiers -> EventLabel,
            ... ] 
    {   
        // many of these may depend on param values
        some (src_state_t1 & s'.confi) // where i is depth of src_state, 
        guard_cond_t1[s'] 
        (s.stable = True) =>
            o1: forall i. not(t1_nonOrthScopei in scopesi) 
            ev1: t1_on  in (s.eventsi :> EnvEvents) + genEventsi // if t1_on is internal this is false
        else {
            o2: forall i. not(t1_nonOrthScopei in scopesi + s'.scopesUsedi) 
            ev2: t1_on  in s.eventsi  + genEventsi
        }
    }
    */
    public static void  addTransIsEnabledAfterStep(DashModule d, String tfqn) {

        String tout = translateFQN(tfqn);
        List<Integer> prsIdx = d.getTransParamsIdx(tfqn); 
        List<String> prs = d.getTransParams(tfqn);
        List<Decl> decls = new ArrayList<Decl>();
        List<Expr> body = new ArrayList<Expr>();

        if (DashOptions.isElectrum) {
            decls.addAll(paramDecls(prsIdx,prs));
        } else {
            decls.addAll(curNextParamsDecls(prsIdx,prs));
        } 
        for (int i=0; i<= d.getMaxDepthParams(); i++) {
            decls.add(scopeDecl(i));
            if (d.hasEventsAti(i)) {
                decls.add(genEventDecl(i));
            }
        }    

        if (!d.hasOnlyOneState())
            // some (p3 -> p2 -> p1 -> src & s'.confi)
            // src does not have to be a basic state  
            body.add(
                createSomeOf(
                    createIntersect(
                        translateDashRefToArrow(d.getTransSrc(tfqn)),
                        nextConf(prsIdx.size()))));

        // primed guard condition is true 
        // TODO

        // orthogonality  ------------------

        // if first step of the big step
        // tfqn's non-orthogonal scope are not in any scopes used in the parameters
        List<Expr> orth1 = new ArrayList<Expr>();
        List<DashRef> nonO = d.nonOrthogonalScopesOf(tfqn);
        for (int i=0;i <= d.getMaxDepthParams(); i++) {
            List<Expr> u = DashRef.hasNumParams(nonO,i).stream()
                .map(x -> translateDashRefToArrow(x))
                .collect(Collectors.toList());
            // o1: forall i. not(t1_nonOrthScopei in scopesi)
            for (Expr x: u) orth1.add(createNot(createIn(x,scopeVar(i))));
        }
        Expr o1 = createAndFromList(orth1);


        // if not the first of the big step
        // tfqn's non-orthogonal scope are not in any scopes used in the parameters + the cur scopes used
        List<Expr> orth2 = new ArrayList<Expr>();
        for (int i=0;i <= d.getMaxDepthParams(); i++) {
            List<Expr> u = DashRef.hasNumParams(nonO,i).stream()
                .map(x -> translateDashRefToArrow(x))
                .collect(Collectors.toList());
            // o2: forall i. not(t1_nonOrthScopei in scopesi + s'.scopesUsedi) 
            for (Expr x: u) orth1.add(createNot(createIn(x,createUnion(curScopesUsed(i), scopeVar(i)))));
        }
        Expr o2 = createAndFromList(orth2);

        // events ----------------------------

        DashRef ev = d.getTransOn(tfqn);
        Expr ev1, ev2;
        if (ev != null) {
            //ev1: t1_on  in (s.eventsi :> EnvEvents) + genEventsi // if t1_on is internal this is false
            if (d.isInternalEvent(ev.getName())) {
                ev1 = createFalse();
            } else {
                ev1 = createIn(
                            translateDashRefToArrow(ev),
                            createUnion(
                                createRangeRes(
                                    curEvents(ev.getParamValues().size()),
                                    allEnvironmentalEventsVar()),
                                genEventVar(ev.getParamValues().size())));
            }
            // ev2: t1_on  in s.eventsi  + genEventsi
            ev2 = createIn(
                        translateDashRefToArrow(ev),
                        createUnion(
                            curEvents(ev.getParamValues().size()),
                            genEventVar(ev.getParamValues().size())));
        } else {
            ev1 = createTrue();
            ev2 = createTrue();
        }

        if (d.hasConcurrency()) 
            body.add(
                createITE(curStableTrue(),
                    createAnd(
                        o1,
                        ev1),
                    createAnd(
                        o2,
                        ev2)));
        else
            body.add(createAnd(o1,ev1));

        d.alloyString += d.addPredSimple(tout+DashStrings.enabledAfterStepName,decls,body);
    }


}