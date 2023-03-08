package ca.uwaterloo.watform.alloyasthelper;

import java.util.Arrays;
import java.util.ArrayList;

import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprVar;

import ca.uwaterloo.watform.alloyasthelper.AlloyExprHelper;

public class AlloyDeclHelper {

    public static Decl createDecl(ExprVar v, Expr e) {
        // not sure if mult is needed on last arg
        return new Decl(null, null, null, null, new ArrayList<>(Arrays.asList(v)) , e);
    }
    public static Decl createOneDecl(String v, String typ) {
        return createDecl(AlloyExprHelper.createVar(v), AlloyExprHelper.createOne(AlloyExprHelper.createVar(typ)));
    }
    public static Decl createSetDecl(String v, String typ) {
        return createDecl(AlloyExprHelper.createVar(v), AlloyExprHelper.createSet(AlloyExprHelper.createVar(typ)));
    }
    
}