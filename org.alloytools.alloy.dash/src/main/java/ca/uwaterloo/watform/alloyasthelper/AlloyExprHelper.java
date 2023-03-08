package ca.uwaterloo.watform.alloyasthelper;

import java.util.ArrayList;
import java.util.Collections;

import edu.mit.csail.sdg.alloy4.Pos;

import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBadJoin;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprITE;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.ExprBinary;

// Expr is not final so we can extend it
public class AlloyExprHelper  {

    public static ExprVar createTrue() {
        return ExprVar.make(Pos.UNKNOWN,  "True");
    } 
    public static ExprVar createVar(String v) {
        return ExprVar.make(Pos.UNKNOWN, v);
    }
    public static ArrayList<ExprVar> createVarList(ArrayList<String> vList) {
        ArrayList<ExprVar> retList = new ArrayList<ExprVar>();
        for (String v: vList) {
            retList.add(createVar(v));
        }
        return retList;
    }

    /* generic ones */
    public static Expr createBinaryExpr(Expr left, ExprBinary.Op op, Expr right) {   
        return (ExprBinary) op.make(Pos.UNKNOWN, Pos.UNKNOWN,left,right);
    }
    public static Expr createUnaryExpr(ExprUnary.Op op, Expr sub) {
        return (ExprUnary) op.make(Pos.UNKNOWN, sub);
    }
    // dunno why this one is different in Alloy code
    public static Expr createExprList(ExprList.Op op, ArrayList<Expr> args) {
        return (ExprList) ExprList.make(Pos.UNKNOWN, Pos.UNKNOWN, op, args);
    }   
    public static Expr createExprQt(ExprQt.Op op, ArrayList<Decl> decls, Expr expr) {
        return op.make(Pos.UNKNOWN, Pos.UNKNOWN, decls,expr);
    }

    /* a few useful specific ones */
    public static Expr createOne(Expr sub) {
        return (ExprUnary) ExprUnary.Op.ONE.make(Pos.UNKNOWN, sub);
    }
    public static Expr createSet(Expr sub) {
        return (ExprUnary) ExprUnary.Op.SETOF.make(Pos.UNKNOWN,  sub);
    }
    public static ExprBinary createJoin(Expr left, Expr right) {
        return (ExprBinary) ExprBinary.Op.JOIN.make(Pos.UNKNOWN, Pos.UNKNOWN, left, right);
    }
    public static Expr createJoinList(ArrayList<Expr> elist) {
        Expr ret = null;
        assert(elist!=null);
        ret = elist.get(0);
        for (Expr el: elist.subList(1,elist.size()-1)) {
            ret = createJoin(ret,el);
        }
        return ret;
    }
    public static Expr createPlusList(ArrayList<Expr> elist) {
        Expr ret = null;
        assert(elist!=null);
        ret = elist.get(0);
        for (Expr el: elist.subList(1,elist.size())) {
            ret = createPlus(ret,el);
        }
        return ret;
    }
    public static ExprBinary createEquals(Expr left, Expr right) {
        return (ExprBinary) ExprBinary.Op.EQUALS.make(Pos.UNKNOWN, Pos.UNKNOWN,  left, right);
    }
    public static ExprBinary createNotEquals(Expr left, Expr right) {
        return (ExprBinary) ExprBinary.Op.NOT_EQUALS.make(Pos.UNKNOWN, Pos.UNKNOWN,  left, right);
    }
    public static ExprBinary createAnd(Expr left, Expr right) {
        return (ExprBinary) ExprBinary.Op.AND.make(Pos.UNKNOWN, Pos.UNKNOWN,  left, right);
    }
    public static Expr createAnd(ArrayList<Expr> args) {
        return (Expr) ExprList.make(Pos.UNKNOWN, Pos.UNKNOWN,  ExprList.Op.AND, args);
    }
    public static ExprBinary createOr(Expr left, Expr right) {
        return (ExprBinary) ExprBinary.Op.OR.make(Pos.UNKNOWN, Pos.UNKNOWN,  left, right);
    }
    public static Expr createOr(ArrayList<Expr> args) {
        return (Expr) ExprList.make(Pos.UNKNOWN, Pos.UNKNOWN,  ExprList.Op.OR, args);
    }
    public static ExprBinary createArrow(Expr left,Expr right) {
        return (ExprBinary) ExprBinary.Op.ARROW.make(Pos.UNKNOWN, Pos.UNKNOWN,  left, right);
    }
    public static ExprBinary createPlus(Expr left,Expr right) {
        return (ExprBinary) ExprBinary.Op.PLUS.make(Pos.UNKNOWN, Pos.UNKNOWN,  left, right);
    }
    public static ExprBinary createIn(Expr left,Expr right) {
        return (ExprBinary) ExprBinary.Op.IN.make(Pos.UNKNOWN, Pos.UNKNOWN,  left, right);
    }
    // {x,y,z}
    // returns x -> (y -> z)
    public static Expr createArrowList(ArrayList<String> eList) {
        assert(eList != null);
        Collections.reverse(eList);
        Expr o = createVar(eList.get(0));
        for (String e: eList.subList(1,eList.size()-1)) {
            o = createArrow(createVar(e), o);
        }
        return o;
    }    


    public static ExprITE createITE(Expr cond, Expr impliesExpr, Expr elseExpr) {
        return (ExprITE) ExprITE.make(Pos.UNKNOWN, cond, impliesExpr, elseExpr);
    }
   
    public static ExprQt createAll(ArrayList<Decl> decls, Expr expr) {
        return (ExprQt) ExprQt.Op.ALL.make(Pos.UNKNOWN, Pos.UNKNOWN,  decls, expr);
    }
    public static ExprQt createSome(ArrayList<Decl> decls, Expr expr) {
        return (ExprQt) ExprQt.Op.SOME.make(Pos.UNKNOWN, Pos.UNKNOWN,  decls, expr);
    }

    public static ExprUnary createAlways(Expr expr) {
        return (ExprUnary) ExprUnary.Op.ALWAYS.make(Pos.UNKNOWN, expr);
    }

}