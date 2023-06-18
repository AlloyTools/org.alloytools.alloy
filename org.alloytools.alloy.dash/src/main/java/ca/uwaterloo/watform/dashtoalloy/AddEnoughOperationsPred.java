/*
 * There exists at least one representative of every transition
 *
 * pred operationsSignificance { 
 *     some s, s’: Snapshot | some p0, p1 | T1[s, s’] 
 *     some s, s’: Snapshot | T2[s, s’] 
 *     some s, s’: Snapshot | T3[s, s’] 
 *     ...
 * }
 */


package ca.uwaterloo.watform.dashtoalloy;

//import java.util.Collections;
//import java.util.stream.Collectors;
import java.util.List;
import java.util.ArrayList;
import java.util.Arrays;

import edu.mit.csail.sdg.ast.Decl;
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

public class AddEnoughOperationsPred {

    public static void addEnoughOperationsPred(DashModule d) {

        ArrayList<Expr> body = new ArrayList<Expr>();

        for (String tfqn: d.getAllTransNames()) {
            String tout = translateFQN(tfqn); 
            body.add(createSome(
                curNextParamsDecls(d.getTransParamsIdx(tfqn),d.getTransParams(tfqn)),
                createPredCall(tout,curNextParamVars(d.getTransParamsIdx(tfqn),d.getTransParams(tfqn)))));
        }
        ArrayList<Decl> nodecls = new ArrayList<Decl>();
        d.alloyString += d.addPredSimple(DashStrings.enoughOperationsName,nodecls, body);
    }
}