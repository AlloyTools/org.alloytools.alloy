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
//import ca.uwaterloo.watform.core.DashUtilFcns;
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

        List<String> prs = d.getAllParams();
        List<Expr> body = new ArrayList<Expr>();
       
        // since this is a fact, we don't need it if there are no invariants 
        if (!d.getInvs().isEmpty()) {
            for (Expr i: d.getInvs())
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
            List<Decl> decls = new ArrayList<Decl>();
            decls.add(curDecl());
            if (!DashOptions.isElectrum) {
                body = new ArrayList<Expr>();
                body.add(createAll(decls,e));
            }
            d.alloyString += d.addFactSimple(DashStrings.invName, body);
        }
    }
}