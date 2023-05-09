package ca.uwaterloo.watform.dashtoalloy;

import java.util.Collections;
import java.util.stream.Collectors;
import java.util.List;
import java.util.ArrayList;
import java.util.Arrays;

import edu.mit.csail.sdg.ast.Decl;
//import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Expr;

import ca.uwaterloo.watform.core.DashOptions;
import ca.uwaterloo.watform.core.DashStrings;
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

public class AddInit {

   // --------------------------------------------------------------------------------------
    /*
        TODO add here
    */        
    public static void addInit(DashModule d) {

        List<String> prs = d.getAllParams();
        List<Expr> body = new ArrayList<Expr>();
        
        // even if these are empty we need this predicate to exist
        for (Expr i: d.getInits())
            // these may have the use of parameters in them
            body.add(translateExpr(i,d));

        // it was really tricky to get these types/lists right
        // so don't try to combine these steps

        Expr e;
        if (!prs.isEmpty())
            e = createAll(
                // might need to add "p" to the front of these
                paramDecls(prs),
                createAndFromList(body));
        else e = createAndFromList(body);
        body = new ArrayList<Expr>();
        body.add(e);
        // init is a reserved word in Electrum
        if (DashOptions.isElectrum) {
            d.alloyString += d.addPredSimple(DashStrings.initFactName, new ArrayList<Decl>(), body);
        } else {
            d.alloyString += d.addPredSimple(DashStrings.initFactName, curNextParamsDecls(prs),body);
        }
    }
}