 package ca.uwaterloo.watform.dashtoalloy;

import java.util.Collections;
import java.util.stream.Collectors;
import java.util.List;
import java.util.ArrayList;
import java.util.Arrays;

//import edu.mit.csail.sdg.ast.Decl;
//import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Expr;

import ca.uwaterloo.watform.core.DashOptions;
import static ca.uwaterloo.watform.core.DashStrings.*;
//import ca.uwaterloo.watform.core.DashUtilFcns;
//import ca.uwaterloo.watform.core.DashRef;

// shortens the code to import these statically
import static ca.uwaterloo.watform.core.DashFQN.*;
import static ca.uwaterloo.watform.alloyasthelper.ExprHelper.*;

//import ca.uwaterloo.watform.alloyasthelper.DeclExt;
//import ca.uwaterloo.watform.alloyasthelper.ExprToString;

import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.parser.CompModuleHelper;

import static ca.uwaterloo.watform.dashtoalloy.Common.*;

public class AddTrans {

   // --------------------------------------------------------------------------------------
    /*
        pred t1[s:Snapshot,s':Snapshot,pparam0:param0,pparam1:param1,pparam2:param2,...] =
            pparam2.pparam1.pparam0.s.pre_1 and
            pparam2.pparam1.pparam0.s'.s.post_1 and
            pparam2.pparam1.pparam0.s'.s'.semantics_t1
    */        
    public static void addTrans(DashModule d, String tfqn) {

        // e.g. [ClientId,ServerId.,,,]
        List<String> prs = d.getTransParams(tfqn);
        List<Expr> body = new ArrayList<Expr>();
        String tout = translateFQN(tfqn); // output FQN
        
        if (DashOptions.isElectrum) {
            // pre_transName[ p0, p1, p2] -> p2.p1.p0.pre_transName
            body.add(createPredCall(tout+ preName, paramVars(prs)));
            // p2.p1.p0.post_transName
            body.add(createPredCall(tout + postName, paramVars(prs)));
            // p2.p1.p0.semantics_transName
            //body.add(createPredCall(tout + semanticsName, paramVars(prs)));
        } else {
            // pre_transName[s, p0, p1, p2] -> p2.p1.p0.s.pre_transName
            body.add(createPredCall(tout + preName, curParamVars(prs)));
            // p2.p1.p0.s'.s.post_transName
            body.add(createPredCall(tout + postName, curNextParamVars(prs)));
            // p2.p1.p0.s'.s.semantics_transName
            //body.add(createPredCall(tout + semanticsName, curNextParamVars(prs)));
        }
        d.alloyString += d.addPredSimple(tout, curNextParamsDecls(prs), body);
    }
}