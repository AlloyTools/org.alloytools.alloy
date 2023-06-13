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

public class AddSmallStep {
    /*
        pred small_step [s:Snapshot, s': Snapshot] { 
                (some pparam0 : Param0 , pparam1 : Param1 ... | 
                    { // for all t’s at level i with params Param5, Param6, ...
                    (or t[s, s_next, pparam5, pparam6 ]) 
                    }) 
                or
                (!(some pparam0 : Param0 , pparam1 : Param1 ... | 
                    { // for all t’s at level i with params Param5, Param6, ...
                    (or t_pre[s, s_next, pparam5, pparam6 ]) )
                    and s = s') 

    */
    public static void addSmallStep(DashModule d) {

        ArrayList<Expr> e = new ArrayList<Expr>();
        List<String> prs = d.getAllParamsInOrder();

        // trans is taken
        for (String tfqn: d.getAllTransNames()) {
            String tout = translateFQN(tfqn); 
            // p3.p2.p1.t for parameters of this transition
            if (DashOptions.isElectrum) e.add(createPredCall(tout,paramVars(d.getTransParamsIdx(tfqn), d.getTransParams(tfqn))));
            // p3.p2.p1.s'.s.t for parameters of this transition
            else e.add(createPredCall(tout,curNextParamVars(d.getTransParamsIdx(tfqn),d.getTransParams(tfqn))));
        }
        Expr transIsTaken;
        if (d.getAllParamsInOrder().isEmpty()) transIsTaken = createOrFromList(e);
        else transIsTaken = createSome(paramDecls(DashUtilFcns.listOfInt(0,prs.size()-1),prs),createOrFromList(e));

        // no trans is enabled
        e = new ArrayList<Expr>();
        for (String tfqn: d.getAllTransNames()) {
            String tout = translateFQN(tfqn); 
            // p3.p2.p1.t for parameters of this transition
            if (DashOptions.isElectrum) e.add(createPredCall(tout,paramVars(d.getTransParamsIdx(tfqn), d.getTransParams(tfqn))));
            // p3.p2.p1.s'.s.t for parameters of this transition
            else e.add(createPredCall(tout+DashStrings.preName,curParamVars(d.getTransParamsIdx(tfqn),d.getTransParams(tfqn))));
        }
        Expr transIsNotEnabled;
        if (d.getAllParamsInOrder().isEmpty()) transIsNotEnabled = createOrFromList(e);
        else transIsNotEnabled = createSome(paramDecls(DashUtilFcns.listOfInt(0,prs.size()-1),prs),createOrFromList(e));
        transIsNotEnabled = createAnd(createNot(transIsNotEnabled), createPredCall(DashStrings.stutterName, curNextVars()));

        e = new ArrayList<Expr>();
        e.add(createOr(transIsTaken, transIsNotEnabled));
        d.alloyString += d.addPredSimple(DashStrings.smallStepName,curNextDecls(),e);
    }
}