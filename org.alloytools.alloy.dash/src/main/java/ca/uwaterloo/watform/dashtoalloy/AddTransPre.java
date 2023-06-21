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

public class AddTransPre {
    // --------------------------------------------------------------------------------------
    /* 
        pred pre_t1[s:Snapshot,pparam0:Param0, ...] {

            some (src_state_t1 & <prs for src_state>.s.conf)
            orthogonal to any scopes uses
            
            guard_cond_t1 [s] 

            s.stable = True => 
                { // beginning of a big step 
                  // transition can be triggered only by environmental events 
                  <prs for trig_event>.trig_events_t1 in (s.events & ExternalEvent ) 
                } else { 
                  // intermediate snapshot 
                  // transition can be triggered by any type of event 
                  <prs for trig_event>.trig_events_t1 in s.events 
                }
            pre of a higher priority transition is not enabled
        }
        Assumption: prs for src state and trig events are a subset of prs for trans
    */
    public static void addTransPre(DashModule d, String tfqn) {
        List<Integer> prsIdx = d.getTransParamsIdx(tfqn); 
        List<String> params = d.getTransParams(tfqn); 
        List<Expr> body = new ArrayList<Expr>();
        String tout = translateFQN(tfqn);

        // p3 -> p2 -> p1 -> src & s.confVar(i) != none
        // src does not have to be a basic state      
        body.add(
            createSomeOf(
                createIntersect(
                    translateDashRefToArrow(d.getTransSrc(tfqn)),
                    curConf(prsIdx.size()))));

        if (d.getTransWhen(tfqn) != null)
            body.add(translateExpr(d.getTransWhen(tfqn),d));

        // has a scope that is orthogonal to any scopes used
        List<DashRef> nonO = d.nonOrthogonalScopesOf(tfqn);
        for (int i=0;i <= d.getMaxDepthParams(); i++) {
            List<Expr> u = DashRef.hasNumParams(nonO,i).stream()
                .map(x -> translateDashRefToArrow(replaceScope(x)))
                .collect(Collectors.toList());
            for (Expr x: u) body.add(createNot(createIn(x,curScopesUsed(i))));
        }

        // event trigger
        // only one triggering event
        if (d.hasConcurrency() && d.getTransOn(tfqn) != null && d.hasEnvironmentalEvents()) {
            // trig_events_t1
            DashRef ev = d.getTransOn(tfqn);
            int sz = ev.getParamValues().size();
            Expr ifBranch;
            if (d.isInternalEvent(ev.getName())) {
                ifBranch = createFalse();
            } else {
                ifBranch = createIn(translateDashRefToArrow(ev),
                        createRangeRes(
                        curEvents(sz), 
                        allEnvironmentalEventsVar()));
            }
            Expr elseBranch = createIn(translateDashRefToArrow(ev), curEvents(sz));
            body.add(createITE(
                curStableTrue(),
                ifBranch,
                elseBranch
            ));
        } else if (d.getTransOn(tfqn) != null) {
            DashRef ev = d.getTransOn(tfqn);
            int sz = ev.getParamValues().size();
            body.add(createIn(translateDashRefToArrow(ev),curEvents(sz)));
        }

        // not a higher priority transition enabled
        List<String> priTrans = d.getHigherPriTrans(tfqn);
        List<Expr> args = new ArrayList<Expr>();
        for (String t:priTrans) {
            // src must directly above this trans in the hierarchy
            // so its parameters must be a subset of the current parameters
            // and we don't need to quantify over them
            args = curParamVars(d.getTransParamsIdx(t), d.getTransParams(t));
            body.add(createNot(createPredCall(translateFQN(t)+DashStrings.preName, args)));
        }
        
        d.alloyString += d.addPredSimple(tout+DashStrings.preName, curParamsDecls(prsIdx,params), body); 
        d.alloyString += "\n";
    }
}