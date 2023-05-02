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
            src_state_t1 in <prs for src_state>.s.conf 
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
        }
        Assumption: prs for src state and trig events are a subset of prs for trans
    */
    public static void addTransPre(DashModule d, String tfqn) {
        List<String> prs = d.getTransParams(tfqn); 
        List<Expr> body = new ArrayList<Expr>();
        String tout = translateFQN(tfqn);

        // p3 -> p2 -> p1 -> src in s.confVar(i)
        // src does not have to be a basic state      
        body.add(createIn(d.getTransSrc(tfqn).toAlloy(),curConf(prs.size())));

        // has a scope that is orthogonal to any scopes used
        List<DashRef> nonO = d.nonOrthogonalScopesOf(tfqn);
        for (int i=0;i <= d.getMaxDepthParams(); i++) {
            List<Expr> u = DashRef.hasNumParams(nonO,i).stream()
                .map(x -> x.toAlloy())
                .collect(Collectors.toList());
            // scopesUsedi' = scopesUsedi - exitedi + enteredi
            Expr e = curConf(i);
            for (Expr x: u) body.add(createNot(createIn(x,scopesUsedVar(i))));
        }

        // event trigger
        // only one triggering event
        if (d.hasConcurrency() && d.getTransOn(tfqn) != null && d.hasEnvironmentalEvents()) {
            // trig_events_t1
            DashRef ev = d.getTransOn(tfqn);
            int sz = ev.getParamValues().size();
            Expr ifBranch = createIn(ev.toAlloy(),
                createIntersect(
                    curEvents(sz), 
                    allEnvironmentalEventsVar()));
            Expr elseBranch = createIn(ev.toAlloy(), curEvents(sz));
            body.add(createITE(
                curStableTrue(),
                ifBranch,
                elseBranch
            ));
        } else if (d.getTransOn(tfqn) != null) {
            DashRef ev = d.getTransOn(tfqn);
            int sz = ev.getParamValues().size();
            body.add(createIn(ev.toAlloy(),curEvents(sz)));
        }
        
        /*
        // TODO
        // guard_cond_t1 [s] 
        o.add(d.getTransGuard(t).convertToAlloy(d.symbolTable, curVar(), nextVar()));
        */

        // not a higher priority transition enabled
        d.alloyString += d.addPredSimple(tout+DashStrings.preName, curParamsDecls(prs), body); 
        d.alloyString += "\n";
    }
}