package ca.uwaterloo.watform.alloyasthelper;

import java.util.ArrayList;
import java.util.List;
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
import edu.mit.csail.sdg.ast.ExprHasName;
import edu.mit.csail.sdg.ast.ExprBinary;


import ca.uwaterloo.watform.core.DashStrings;

// these are all static
// don't want to make them an extension
// because then would have to put them in all different classes


public class ExprHelper  {

    // useful in development
    public static Expr createNullExpr() {
        return createEquals(createTrue(),createTrue());
    }
    public static ExprVar createTrue() {
        return ExprVar.make(Pos.UNKNOWN,  DashStrings.trueName);
    } 
    public static ExprVar createNone() {
        return ExprVar.make(Pos.UNKNOWN,  DashStrings.noneName);
    } 
    public static ExprVar createVar(String v) {
        return ExprVar.make(Pos.UNKNOWN, v);
    }
    public static List<ExprVar> createVarList(List<String> vList) {
        List<ExprVar> retList = new ArrayList<ExprVar>();
        for (String v: vList) {
            retList.add(createVar(v));
        }
        return retList;
    }
    public static List<ExprVar> createVarList(String prefix, List<String> vList) {
        List<ExprVar> retList = new ArrayList<ExprVar>();
        for (String v: vList) {
            retList.add(createVar(prefix+v));
        }
        return retList;
    }
    // to avoid the need to cast every ExprVar to an Expr
    public static List<Expr> createVarExprList(String prefix, List<String> vList) {
        List<Expr> retList = new ArrayList<Expr>();
        for (String v: vList) {
            retList.add((Expr) createVar(prefix+v));
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
    public static Expr createExprList(ExprList.Op op, List<Expr> args) {
        return (ExprList) ExprList.make(Pos.UNKNOWN, Pos.UNKNOWN, op, args);
    }   
    public static Expr createExprQt(ExprQt.Op op, List<Decl> decls, Expr expr) {
        return op.make(Pos.UNKNOWN, Pos.UNKNOWN, decls,expr);
    }

    /* a few useful specific ones */
    public static Expr createNot(Expr sub) {
        return (ExprUnary) ExprUnary.Op.NOT.make(Pos.UNKNOWN, sub);
    }
    public static Expr createOne(Expr sub) {
        return (ExprUnary) ExprUnary.Op.ONE.make(Pos.UNKNOWN, sub);
    }
    public static Expr createSet(Expr sub) {
        return (ExprUnary) ExprUnary.Op.SETOF.make(Pos.UNKNOWN,  sub);
    }
    public static ExprBinary createJoin(Expr left, Expr right) {
        return (ExprBinary) ExprBinary.Op.JOIN.make(Pos.UNKNOWN, Pos.UNKNOWN, left, right);
    }
    public static Expr createJoinList(List<Expr> elist) {
        Expr ret = null;
        assert(elist!=null);
        Collections.reverse(elist);
        ret = elist.get(0);
        for (Expr el: elist.subList(1,elist.size())) {
            ret = createJoin(ret,el);
        }
        return ret;
    }
    public static Expr createUnionList(List<Expr> elist) {
        Expr ret = null;
        assert(elist!=null);
        ret = elist.get(0);
        for (Expr el: elist.subList(1,elist.size())) {
            ret = createUnion(ret,el);
        }
        return ret;
    }
    public static ExprBinary createEquals(Expr left, Expr right) {
        return (ExprBinary) ExprBinary.Op.EQUALS.make(Pos.UNKNOWN, Pos.UNKNOWN,  left, right);
    }
    public static ExprBinary createNotEquals(Expr left, Expr right) {
        return (ExprBinary) ExprBinary.Op.NOT_EQUALS.make(Pos.UNKNOWN, Pos.UNKNOWN,  left, right);
    }
    // returns an ExprList
    public static ExprList createAnd(Expr left, Expr right) {
        return (ExprList) ExprBinary.Op.AND.make(Pos.UNKNOWN, Pos.UNKNOWN,  left, right);
    }
    public static ExprList createAnd(List<Expr> args) {
        return (ExprList) ExprList.make(Pos.UNKNOWN, Pos.UNKNOWN,  ExprList.Op.AND, args);
    }
    public static ExprList createOr(Expr left, Expr right) {
        return (ExprList) ExprBinary.Op.OR.make(Pos.UNKNOWN, Pos.UNKNOWN,  left, right);
    }
    public static ExprList createOr(List<Expr> args) {
        return (ExprList) ExprList.make(Pos.UNKNOWN, Pos.UNKNOWN,  ExprList.Op.OR, args);
    }
    public static ExprBinary createArrow(Expr left,Expr right) {
        return (ExprBinary) ExprBinary.Op.ARROW.make(Pos.UNKNOWN, Pos.UNKNOWN,  left, right);
    }
    // set union
    public static ExprBinary createUnion(Expr left,Expr right) {
        return (ExprBinary) ExprBinary.Op.PLUS.make(Pos.UNKNOWN, Pos.UNKNOWN,  left, right);
    }
    // set diff
    public static ExprBinary createDiff(Expr left,Expr right) {
        return (ExprBinary) ExprBinary.Op.MINUS.make(Pos.UNKNOWN, Pos.UNKNOWN,  left, right);
    }
    public static ExprBinary createIn(Expr left,Expr right) {
        return (ExprBinary) ExprBinary.Op.IN.make(Pos.UNKNOWN, Pos.UNKNOWN,  left, right);
    }
    // {x,y,z}
    // returns x -> (y -> z)
    public static Expr createArrowList(List<String> eList) {
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
   
    public static ExprQt createAll(List<Decl> decls, Expr expr) {
        return (ExprQt) ExprQt.Op.ALL.make(Pos.UNKNOWN, Pos.UNKNOWN,  decls, expr);
    }
    public static ExprQt createSome(List<Decl> decls, Expr expr) {
        return (ExprQt) ExprQt.Op.SOME.make(Pos.UNKNOWN, Pos.UNKNOWN,  decls, expr);
    }

    public static ExprUnary createAlways(Expr expr) {
        return (ExprUnary) ExprUnary.Op.ALWAYS.make(Pos.UNKNOWN, expr);
    }

    public static Expr createPredCall(String name, List<Expr> elist) {
        // using ExprCall.make is overkill
        // b/c it required the entire function definition to be passed
        // as an argument
        // joins are equivalent but not as nice to look at :-)
        // order of joins is tricky
        Expr o = createVar(name);
        for (Expr e:elist) {
            o = createJoin(e,o);
        }
        return o;
    }

    // simple equality: two var names are equal
    public static boolean sEquals(Expr e1, Expr e2) {
        return ( (e1 == e2) ||
                 (e1 instanceof ExprVar && 
                    e2 instanceof ExprVar && 
                    ((ExprVar) e1).label.equals(((ExprVar) e2).label))) ;
    }

}