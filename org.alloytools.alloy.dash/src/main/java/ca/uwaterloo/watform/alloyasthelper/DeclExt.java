package ca.uwaterloo.watform.alloyasthelper;

import java.util.*;
import java.util.Arrays;
import java.util.ArrayList;
import java.util.StringJoiner;

import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprVar;

import ca.uwaterloo.watform.core.DashErrors;

import ca.uwaterloo.watform.alloyasthelper.ExprHelper;

public class DeclExt extends Decl {

    public DeclExt(ExprVar v, Expr e) {
        super(null, null, null, null, new ArrayList<>(Arrays.asList(v)) , e);
    }
    public String toString() {
        // Decl does not have a toString()
        String x = new String();
        StringJoiner sj = new StringJoiner(", ");
        names.forEach(n -> sj.add(n.toString()));
        x += sj.toString();
        x += " : ";
        x += expr.toString();
        return x;
    }

    public DeclExt(String v, Expr e) {
        // not sure if mult is needed on last arg
        super(null, null, null, null, new ArrayList<>(Arrays.asList(ExprHelper.createVar(v))) , e);
    }
    // default is "one"
    public DeclExt(String v, String typ) {
        super(null, null, null, null, new ArrayList<>(Arrays.asList(ExprHelper.createVar(v))), ExprHelper.createOne(ExprHelper.createVar(typ)));
    }
    public static DeclExt newOneDeclExt(String v, String typ) {
        return new DeclExt(v, ExprHelper.createOne(ExprHelper.createVar(typ)));
    }
    public static DeclExt newOneDeclExt(String v, Expr typ) {
        return new DeclExt(v, typ);
    }
    public static DeclExt newSetDeclExt(String v, String typ) {
        return new DeclExt(v, ExprHelper.createSet(ExprHelper.createVar(typ)));
    }
    public static DeclExt newSetDeclExt(String v, Expr typ) {
        return new DeclExt(v, typ);
    }
}