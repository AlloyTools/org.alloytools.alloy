package ca.uwaterloo.watform.dashtoalloy;

//import java.util.Collections;
//import java.util.stream.Collectors;
import java.util.List;
import java.util.ArrayList;
import java.util.Arrays;

//import edu.mit.csail.sdg.ast.Decl;
//import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Expr;

import ca.uwaterloo.watform.core.DashOptions;
import ca.uwaterloo.watform.core.DashStrings;
import ca.uwaterloo.watform.core.DashUtilFcns;
//import ca.uwaterloo.watform.core.DashRef;

// shortens the code to import these statically
import static ca.uwaterloo.watform.core.DashFQN.*;
import static ca.uwaterloo.watform.alloyasthelper.ExprHelper.*;

//import ca.uwaterloo.watform.alloyasthelper.DeclExt;
//import ca.uwaterloo.watform.alloyasthelper.ExprToString;

import ca.uwaterloo.watform.parser.DashModule;
//import ca.uwaterloo.watform.parser.CompModuleHelper;

import static ca.uwaterloo.watform.dashtoalloy.Common.*;

public class AddAllSnapshotsDifferentFact {
    /*
        fact allSnapshotsDifferent {
            all s:DshSnapshot, sn:DshSnapshot |
                s.dsh_sc_used0 = sn.dsh_sc_used0 and
                s.dsh_conf0 = sn.dsh_conf0 and
                s.dsh_taken0 = sn.dsh_taken0 and
                s.dsh_events0 = sn.dsh_events0 and
                s.dsh_stable = sn.dsh_stable =>
            s = sn
        }
    */
    public static void addAllSnapshotsDifferentFact(DashModule d) {
        List<Expr> body = new ArrayList<Expr>();
        Expr e;
        for (int i = 0; i <= d.getMaxDepthParams(); i++) {
            if (!d.hasOnlyOneState())
                body.add(createEquals(curConf(i),nextConf(i)));
            // s.scopesUsedi = sn.scopesUsedi
            if (d.hasConcurrency())
                body.add(createEquals(curScopesUsed(i),nextScopesUsed(i)));
            body.add(createEquals(curTransTaken(i),nextTransTaken(i)));
            if (d.hasInternalEventsAti(i))
                body.add(createEquals(curEvents(i),nextEvents(i)));
        }
        if (d.hasConcurrency())
            body.add(createEquals(curStable(),nextStable()));
        List<String> allVarsAndBuffers = d.getAllVarNames();
        allVarsAndBuffers.addAll(d.getAllBufferNames());
        for (String v: allVarsAndBuffers) {
            body.add(createEquals(curJoinExpr(createVar(translateFQN(v))), nextJoinExpr(createVar(translateFQN(v)))));
        }

        //TODO: have to add something for all dynamic variables !!!!
        e = createAll(curNextDecls(), createImplies(createAndList(body), createEquals(curVar(), nextVar())));
        body = new ArrayList<Expr>();
        body.add(e);
        d.alloyString += d.addFactSimple(DashStrings.allSnapshotsDifferentName, body);
    }
}