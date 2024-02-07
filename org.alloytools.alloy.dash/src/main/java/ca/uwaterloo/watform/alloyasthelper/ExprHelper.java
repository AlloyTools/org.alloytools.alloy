package ca.uwaterloo.watform.alloyasthelper;

import java.util.ArrayList;
import java.util.List;
import java.util.Collections;
import java.util.stream.Collectors;

import edu.mit.csail.sdg.alloy4.Pos;

import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBadJoin;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprITE;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.ExprLet;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.ExprHasName;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprCall;
import edu.mit.csail.sdg.ast.ExprChoice;
import edu.mit.csail.sdg.ast.ExprConstant;

import ca.uwaterloo.watform.core.DashStrings;
import ca.uwaterloo.watform.core.DashErrors;
import ca.uwaterloo.watform.core.DashUtilFcns;
import ca.uwaterloo.watform.alloyasthelper.ExprToString;

// these are all static
// don't want to make them an extension
// because then would have to put them in all different classes


public class ExprHelper  {

    // tests ------------------------------------
    public static boolean isExprBinary(Expr e) {
        return (e instanceof ExprBinary);
    }
    public static boolean isExprUnary(Expr e) {
        return (e instanceof ExprUnary);
    }
    public static boolean isExprSet(Expr e) {
        return ((e instanceof ExprUnary) && ((ExprUnary) e).op.equals(ExprUnary.Op.SETOF));
    }
    public static boolean isExprOne(Expr e) {
        return ((e instanceof ExprUnary) && ((ExprUnary) e).op.equals(ExprUnary.Op.ONE));
    }
    public static boolean isExprOneOf(Expr e) {
        return ((e instanceof ExprUnary) && ((ExprUnary) e).op.equals(ExprUnary.Op.ONEOF));
    }
    public static boolean isExprLone(Expr e) {
        return ((e instanceof ExprUnary) && ((ExprUnary) e).op.equals(ExprUnary.Op.LONE));
    }
    public static boolean isExprCard(Expr e) {
        return ((e instanceof ExprUnary) && ((ExprUnary) e).op.equals(ExprUnary.Op.CARDINALITY));
    }
 
    public static boolean isExprRClosure(Expr e) {
        return ((e instanceof ExprUnary) && ((ExprUnary) e).op.equals(ExprUnary.Op.RCLOSURE));
    }

    public static boolean isExprClosure(Expr e) {
        return ((e instanceof ExprUnary) && ((ExprUnary) e).op.equals(ExprUnary.Op.CLOSURE));
    }


    public static boolean isExprJoin(Expr e) {
        return ((e instanceof ExprBinary) && ((ExprBinary) e).op.equals(ExprBinary.Op.JOIN));
    }
    public static boolean isExprArrow(Expr e) {
        return ((e instanceof ExprBinary) && ((ExprBinary) e).op.equals(ExprBinary.Op.ARROW));
    }
    public static boolean isExprBadJoin(Expr e) {
        return (e instanceof ExprBadJoin);
    }
    public static boolean isExprVar(Expr e) {
        return (e instanceof ExprVar);
    }

    public static boolean isPrimedVar(Expr e) {
        return (e instanceof ExprUnary &&
                ((ExprUnary) e).sub instanceof ExprVar &&
                ((ExprUnary) e).op == ExprUnary.Op.PRIME);
    }

    // simple equality: two var names are equal -----------------------
    public static boolean sEquals(Expr e1, Expr e2) {
        return ( (e1 == e2) ||
                 (isExprVar(e1) && isExprVar(e2) && 
                    getVarName((ExprVar) e1).equals(getVarName((ExprVar) e2)))) ;
    }

    // destructors -------------------------------
    public static String getVarName(ExprVar e) {
        return e.label;
    }

    public static Expr getRight(Expr e) {
        if (isExprBinary(e))
            return ((ExprBinary) e).right;
        else if (isExprBadJoin(e) )
            return ((ExprBadJoin) e).right;
        else if (e instanceof ExprITE)
            return ((ExprITE) e).right;
        else { DashErrors.getRightNotBinaryOrJoin(e.getClass().getName()); return null; }
    }
    public static Expr getLeft(Expr e) {
        if (isExprBinary(e)) 
            return ((ExprBinary) e).left;
        else if (isExprBadJoin(e))
            return ((ExprBadJoin) e).left;
        else if (e instanceof ExprITE)
            return ((ExprITE) e).left;
        else { DashErrors.getLeftNotBinaryOrJoin(e.getClass().getName()); return null; }
    }

    public static Expr getSub(Expr e) {
        if (isExprUnary(e)) {
            return ((ExprUnary) e).sub;
        } else {
            DashErrors.getSubNotUnary(e.getClass().getName()); return null; 
        }
    }
    public static ExprBinary.Op getBinaryOp(Expr e) {
        assert(e instanceof ExprBinary);
        return ((ExprBinary) e).op;
    }
    public static ExprUnary.Op getUnaryOp(Expr e) {
        assert(e instanceof ExprUnary);
        return ((ExprUnary) e).op;
    }
    public static Expr getCond(Expr e) {
        assert(e instanceof ExprITE);
        return ((ExprITE) e).cond;
    }

    // constructors -----------------------------------

    // useful in development
    public static Expr createNullExpr() {
        return createEquals(createTrue(),createTrue());
    }
    public static ExprVar createTrue() {
        return ExprVar.make(Pos.UNKNOWN,  DashStrings.trueName);
    } 
    public static Expr createIsTrue(Expr e) {
        List<Expr> elist = new ArrayList<Expr>();
        elist.add(e);
        return createPredCall(DashStrings.isTrue,elist);
    }
    public static Expr createIsFalse(Expr e) {
        List<Expr> elist = new ArrayList<Expr>();
        elist.add(e);
        return createPredCall(DashStrings.isFalse,elist);
    }
    public static ExprVar createFalse() {
        return ExprVar.make(Pos.UNKNOWN,  DashStrings.falseName);
    } 
    public static ExprVar createNone() {
        return ExprVar.make(Pos.UNKNOWN,  DashStrings.noneName);
    } 
    public static ExprVar createVar(String v) {
        return ExprVar.make(Pos.UNKNOWN, v);
    }
    public static ExprVar createVar(Pos p, String v) {
        return ExprVar.make(p, v);
    }
    public static List<Expr> createVarList(List<String> vList) {
        List<Expr> retList = new ArrayList<Expr>();
        for (String v: vList) {
            retList.add(createVar(v));
        }
        return retList;
    }
    public static List<Expr> createVarList(String prefix, List<String> vList) {
        List<Expr> retList = new ArrayList<Expr>();
        for (String v: vList) {
            retList.add(createVar(prefix+v));
        }
        return retList;
    }


    
    // to avoid the need to cast every ExprVar to an Expr
    public static List<ExprVar> createExprVarList(List<String> vList) {
        List<ExprVar> retList = new ArrayList<ExprVar>();
        for (String v: vList) {
            retList.add((ExprVar) createVar(v));
        }
        return retList;
    }
    public static List<ExprVar> createExprVarList(String prefix, List<String> vList) {
        List<ExprVar> retList = new ArrayList<ExprVar>();
        for (String v: vList) {
            retList.add((ExprVar) createVar(prefix + v));
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
    public static Expr createPrime(Expr sub) {
        return ExprUnary.Op.PRIME.make(Pos.UNKNOWN, sub);
    }

    public static Expr createExprList(ExprList.Op op, List<Expr> args) {
        return (Expr) ExprList.make(Pos.UNKNOWN, Pos.UNKNOWN, op, args);
    }   
    public static Expr createExprQt(ExprQt.Op op, List<Decl> decls, Expr expr) {
        return op.make(Pos.UNKNOWN, Pos.UNKNOWN, decls,expr);
    }

    /* a few useful specific ones */
    public static Expr createNoop(Expr sub) {
        return (ExprUnary) ExprUnary.Op.NOOP.make(Pos.UNKNOWN, sub);
    }
    public static Expr createNot(Expr sub) {
        return (ExprUnary) ExprUnary.Op.NOT.make(Pos.UNKNOWN, sub);
    }
    public static Expr createOne(Expr sub) {
        return (ExprUnary) ExprUnary.Op.ONE.make(Pos.UNKNOWN, sub);
    }
    public static Expr createOneOf(Expr sub) {
        return (ExprUnary) ExprUnary.Op.ONEOF.make(Pos.UNKNOWN, sub);
    }
    public static Expr createLone(Expr sub) {
        return (ExprUnary) ExprUnary.Op.LONE.make(Pos.UNKNOWN, sub);
    }
    public static Expr createSomeOf(Expr sub) {
        return (ExprUnary) ExprUnary.Op.SOMEOF.make(Pos.UNKNOWN, sub);
    }
    public static Expr createNo(Expr sub) {
        return (ExprUnary) ExprUnary.Op.NO.make(Pos.UNKNOWN, sub);
    }
    public static Expr createSet(Expr sub) {
        return (ExprUnary) ExprUnary.Op.SETOF.make(Pos.UNKNOWN,  sub);
    }
    public static ExprUnary createReflexiveTransitiveClosure(Expr sub) {
        return (ExprUnary) ExprUnary.Op.RCLOSURE.make(Pos.UNKNOWN, sub);
    }
    public static ExprBinary createJoin(Expr left, Expr right) {
        return (ExprBinary) ExprBinary.Op.JOIN.make(Pos.UNKNOWN, Pos.UNKNOWN, left, right);
    }
    public static ExprBinary createJoin(Pos p, Expr left, Expr right) {
        return (ExprBinary) ExprBinary.Op.JOIN.make(p, p, left, right);
    }
    public static Expr createJoinList(List<Expr> elist) {
        Expr ret = null;
        assert(elist!=null);
        Collections.reverse(elist);
        ret = elist.get(0);
        for (Expr el: elist.subList(1,elist.size())) {
            ret = createJoin(el,ret);
        }
        return ret;
    }
    public static Expr createJoinList(List<Expr> elist, Expr e) {
        assert(elist!=null);
        Collections.reverse(elist);
        Expr ret = e;
        for (Expr el: elist) {
            ret = createJoin(el,ret);
        }
        return ret;
    }
    public static ExprBinary createRangeRes(Expr left, Expr right) {
        return (ExprBinary) ExprBinary.Op.RANGE.make(Pos.UNKNOWN, Pos.UNKNOWN, left, right);
    }
    public static ExprBinary createDomainRes(Expr left, Expr right) {
        return (ExprBinary) ExprBinary.Op.DOMAIN.make(Pos.UNKNOWN, Pos.UNKNOWN, left, right);
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
    public static Expr createDiffList(List<Expr> elist) {
        Expr ret = null;
        assert(elist!=null);
        ret = elist.get(0);
        for (Expr el: elist.subList(1,elist.size())) {
            ret = createDiff(ret,el);
        }
        return ret;
    }
    public static Expr createEquals(Expr left, Expr right) {
        if (sEquals(left,right)) return (Expr) createTrue();
        else return (Expr) ExprBinary.Op.EQUALS.make(Pos.UNKNOWN, Pos.UNKNOWN,  left, right);
    }
    public static ExprBinary createNotEquals(Expr left, Expr right) {
        return (ExprBinary) ExprBinary.Op.NOT_EQUALS.make(Pos.UNKNOWN, Pos.UNKNOWN,  left, right);
    }

    public static Expr createAnd(Expr left, Expr right) {
        if (sEquals(left, createFalse())) return createFalse();
        if (sEquals(right, createFalse())) return createFalse();
        if (sEquals(left, createTrue())) return right;
        if (sEquals(right, createTrue())) return left;
        return (Expr) ExprBinary.Op.AND.make(Pos.UNKNOWN, Pos.UNKNOWN,  left, right);
    }
    public static Expr createAndList(List<Expr> args) {
        //TODO put simplifications in here
        return (Expr) ExprList.make(Pos.UNKNOWN, Pos.UNKNOWN,  ExprList.Op.AND, args);
    }

    public static Expr createAndFromList(List<Expr> elist) {
        // does simplifications
        if (elist.isEmpty()) return createTrue();
        Expr ret = elist.get(0);
        for (Expr el: elist.subList(1,elist.size())) {
            ret = createAnd(ret,el);
        }
        return ret;
    }
    public static Expr createOr(Expr left, Expr right) {
        if (sEquals(left, createTrue())) return createTrue();
        if (sEquals(right, createTrue())) return createTrue();
        if (sEquals(left, createFalse())) return right;
        if (sEquals(right, createFalse())) return left;
        return (Expr) ExprBinary.Op.OR.make(Pos.UNKNOWN, Pos.UNKNOWN,  left, right);
    }
    public static Expr createOrFromList(List<Expr> elist) {
        if (elist.isEmpty()) return createTrue();
        Expr ret = elist.get(0);
        for (Expr el: elist.subList(1,elist.size())) {
            ret = createOr(ret,el);
        }
        return ret;
    }
    public static ExprList createOrList(List<Expr> args) {
        // put simplifications in here so can replace createOrFromList
        return (ExprList) ExprList.make(Pos.UNKNOWN, Pos.UNKNOWN,  ExprList.Op.OR, args);
    }
    public static Expr createIff(Expr left, Expr right) {
        return (Expr) ExprBinary.Op.IFF.make(Pos.UNKNOWN, Pos.UNKNOWN,  left, right);
    }
    public static Expr createImplies(Expr left, Expr right) {
        return (Expr) ExprBinary.Op.IMPLIES.make(Pos.UNKNOWN, Pos.UNKNOWN,  left, right);
    }
    public static ExprBinary createArrow(Expr left,Expr right) {
        return (ExprBinary) ExprBinary.Op.ARROW.make(Pos.UNKNOWN, Pos.UNKNOWN,  left, right);
    }
    // set union
    public static ExprBinary createUnion(Expr left,Expr right) {
        return (ExprBinary) ExprBinary.Op.PLUS.make(Pos.UNKNOWN, Pos.UNKNOWN,  left, right);
    }
    public static Expr createUnionFromList(List<Expr> elist) {
        //TODO make an ExprList
        if (elist.isEmpty()) return createNone();
        Expr ret = elist.get(0);
        for (Expr el: elist.subList(1,elist.size())) {
            ret = createUnion(ret,el);
        }
        return ret;
    }
    public static ExprBinary createIntersect(Expr left,Expr right) {
        return (ExprBinary) ExprBinary.Op.INTERSECT.make(Pos.UNKNOWN, Pos.UNKNOWN,  left, right);
    }
    // set diff
    public static ExprBinary createDiff(Expr left,Expr right) {
        return (ExprBinary) ExprBinary.Op.MINUS.make(Pos.UNKNOWN, Pos.UNKNOWN,  left, right);
    }
    public static ExprBinary createIn(Expr left,Expr right) {
        return (ExprBinary) ExprBinary.Op.IN.make(Pos.UNKNOWN, Pos.UNKNOWN,  left, right);
    }
    public static ExprBinary createNotIn(Expr left,Expr right) {
        return (ExprBinary) ExprBinary.Op.NOT_IN.make(Pos.UNKNOWN, Pos.UNKNOWN,  left, right);
    }
    // {x,y,z}
    // returns x -> (y -> z)
    public static Expr createArrowStringList(List<String> eList) {
        assert(eList != null);
        Collections.reverse(eList);
        Expr o = createVar(eList.get(0));
        for (String e: eList.subList(1,eList.size())) {
            o = createArrow(createVar(e), o);
        }
        return o;
    }    
    public static Expr createArrowExprList(List<Expr> eList) {
        assert(!eList.isEmpty());
        //System.out.println("input " + eList);
        List<Expr> xList = DashUtilFcns.reverse(eList);
        //assert(!xList.isEmpty());
        //System.out.println("reversed: " +xList);
        Expr o = xList.get(0);
        if (xList.size() == 1) return o;
        else {
            for (Expr x: xList.subList(1,xList.size())) {
                o = createArrow(x, o);
            }
        }
        return o;
    }   

    // Alloy won't use boolean/True or boolean/False as formulas
    // but it can be convenient in our code to use them
    // so let's just simplify them out in formulas
    public static Expr createITE(Expr cond, Expr impliesExpr, Expr elseExpr) {
        if (sEquals(cond, createTrue()))  return (Expr) impliesExpr;
        if (sEquals(cond,createFalse())) return (Expr) elseExpr;
        if (sEquals(impliesExpr,createTrue())) return createOr(cond, createAnd(createNot(cond),elseExpr));
        if (sEquals(impliesExpr,createFalse())) return createAnd(createNot(cond),elseExpr);
        if (sEquals(elseExpr,createTrue())) return createOr(createAnd(cond,impliesExpr), createNot(cond));
        if (sEquals(elseExpr,createFalse())) return createAnd(cond,impliesExpr);
        else return (Expr) ExprITE.make(Pos.UNKNOWN, cond, impliesExpr, elseExpr);
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

    /* these wrap the object creation and call to the pretty printer */
    public static String ppExpr(Expr e) {
        ExprToString eToString = new ExprToString(false);
        return eToString.exprToString(e);
    }

    public static String ppDecl(Decl d) {
        ExprToString eToString = new ExprToString(false);
        return eToString.declToString(d);
    }

    public static boolean usedIn(Expr v, Expr exp) {

        assert(isExprVar(v));
        if (isExprVar(exp)) {
            return (getVarName((ExprVar) exp).equals(getVarName((ExprVar) v)));
        }
        else if (isExprBinary(exp) || isExprBadJoin(exp)) {
            return (usedIn(v,getLeft(exp)) || usedIn(v,getRight(exp)));
        } else if (exp instanceof ExprCall) {
            for (Expr e: ((ExprCall) exp).args) 
                if (usedIn(v,e)) return true;
            return false;
        } else if (exp instanceof ExprChoice){
            for (Expr e: ((ExprChoice) exp).choices)
                if (usedIn(v,e)) return true;
            return false;
        } else if (exp instanceof ExprITE){
            return (usedIn(v,getCond(exp)) || usedIn(v,getLeft(exp)) || usedIn(v, getRight(exp)));
        } else if (exp instanceof ExprList){
            for (Expr e: ((ExprList) exp).args) 
                if (usedIn(v,e)) return true;
            return false;
        } else if (exp instanceof ExprUnary){
            return usedIn(v,((ExprUnary) exp).sub);
        } else if (exp instanceof ExprLet){
            return usedIn(v,(((ExprLet) exp).expr)) || usedIn(v,((ExprLet) exp).sub);
        } else if (exp instanceof ExprQt){
            List<Expr> ll = ((ExprQt) exp).decls.stream()
                .map(i -> i.expr)
                .collect(Collectors.toList());
            for (Expr e: ll) if (usedIn(v,e)) return true;
            return false;
        } else if (exp instanceof ExprConstant){
            return false;
        } else {
            DashErrors.UnsupportedExpr("usedIn", "");
            return false;
        }        
    }
}