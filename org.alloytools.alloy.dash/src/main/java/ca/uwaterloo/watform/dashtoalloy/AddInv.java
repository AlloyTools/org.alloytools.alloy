package ca.uwaterloo.watform.dashtoalloy;

import java.util.Arrays;
import java.util.ArrayList;
import java.util.Collections;
import java.util.stream.Collectors;
import java.util.List;



import edu.mit.csail.sdg.ast.Decl;
//import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Expr;

import ca.uwaterloo.watform.core.DashOptions;
import ca.uwaterloo.watform.core.DashStrings;
import ca.uwaterloo.watform.core.DashUtilFcns;
//import ca.uwaterloo.watform.core.DashRef;

// shortens the code to import these statically
//import static ca.uwaterloo.watform.core.DashFQN.*;


//import ca.uwaterloo.watform.alloyasthelper.DeclExt;
//import ca.uwaterloo.watform.alloyasthelper.ExprToString;

import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.parser.CompModuleHelper;

import static ca.uwaterloo.watform.alloyasthelper.ExprHelper.*;
import static ca.uwaterloo.watform.dashtoalloy.Common.*;

public class AddInv {

   // --------------------------------------------------------------------------------------
    /*
        TODO add here
    */        
    public static void addInv(DashModule d) {

        List<String> prs = d.getAllParamsInOrder();
        List<Expr> body = new ArrayList<Expr>();
       
        // since this is a fact, we don't need it if there are no invariants 
        if (!d.getInvs().isEmpty()) {
            for (Expr i: d.getInvs())
                // these may have the use of parameters in them
                body.add(translateExpr(i,d));

            // it was really tricky to get these types/lists right
            // so don't try to combine these steps

            Expr e;
            List<Decl> decls = new ArrayList<Decl>();
            if (!body.isEmpty()) {
                if (!prs.isEmpty()) {
                    // all parameters are not used in inv
                    e = createAndFromList(body);
                    for (int i=0; i < prs.size();i++) {
                        if (usedIn(paramVar(i,prs.get(i)),e )) {
                            decls.add(paramDecl(i,prs.get(i)));
                        }
                    }
                    if (!decls.isEmpty()) e = createAll(decls,e);
                }
                else e = createAndFromList(body);
                body = new ArrayList<Expr>();
                body.add(e);
            } else e = createAndFromList(body);
            if (usedIn(curVar(),e)) decls.add(curDecl());
            if (!DashOptions.isElectrum) {
                body = new ArrayList<Expr>();
                if (!decls.isEmpty()) body.add(createAll(decls,e));
                else body.add(e);
            }
            d.alloyString += d.addFactSimple(DashStrings.invName, body);
        }
    }
}