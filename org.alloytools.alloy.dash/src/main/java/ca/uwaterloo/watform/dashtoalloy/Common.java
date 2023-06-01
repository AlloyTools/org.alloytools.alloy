package ca.uwaterloo.watform.dashtoalloy;

import java.util.Collections;
import java.util.stream.Collectors;
import java.util.List;
import java.util.ArrayList;
import java.util.Arrays;

//import edu.mit.csail.sdg.ast.Decl;
//import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.*;
import edu.mit.csail.sdg.alloy4.ConstList;

import ca.uwaterloo.watform.core.DashOptions;
import ca.uwaterloo.watform.core.DashStrings;
import ca.uwaterloo.watform.core.DashUtilFcns;
import ca.uwaterloo.watform.core.DashRef;
import ca.uwaterloo.watform.core.DashErrors;


// shortens the code to import these statically
import static ca.uwaterloo.watform.core.DashFQN.*;
import static ca.uwaterloo.watform.alloyasthelper.ExprHelper.*;

import ca.uwaterloo.watform.alloyasthelper.DeclExt;
import ca.uwaterloo.watform.alloyasthelper.ExprToString;

import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.parser.CompModuleHelper;

public class Common {

    // s:Snapshot
    public static Decl curDecl() {
        return (Decl) new DeclExt(DashStrings.curName, DashStrings.snapshotName);
    }


    // s':Snapshot
    public static Decl nextDecl() {
        return (Decl) new DeclExt(DashStrings.nextName, DashStrings.snapshotName);
    }


    // p0:P0
    public static Decl paramDecl(Integer n, String name) {
        return (Decl) new DeclExt(DashStrings.pName+n+"_"+name, name);
    }

    //pi: Identfiers
    //public static Decl posParamDecl(Integer i) {
    //    return (Decl) new DeclExt(DashStrings.pName+Integer.toString(i), DashStrings.identifierName);
    //}

    // [s:Snapshot, s':Snapshot] 
    public static List<Decl> curNextDecls() {
        List<Decl> o = new ArrayList<Decl>();
        if (!DashOptions.isElectrum) {
            o.add(curDecl());
            o.add(nextDecl());
        }
        return o;
    }

    // [p0:P0, p1:P1, ...]
    public static List<Decl> paramDecls(List<Integer> prsIdx , List<String> prs) {
        List<Decl> o = new ArrayList<Decl>();
        for (int i=0;i<prsIdx.size();i++) o.add(paramDecl(prsIdx.get(i),  prs.get(i)));
        return o;
    }

    // s:Snapshot, p0:P0, p1:P1, ...]
    public static List<Decl> curParamsDecls(List<Integer> prsIdx, List<String> prs) {
        List<Decl> o = new ArrayList<Decl>();
        if (!DashOptions.isElectrum) o.add(curDecl());
        o.addAll(paramDecls(prsIdx,  prs));
        return o;
    }
    // s:Snapshot, s':Snapshot, p0:P0, p1:P1, ...]
    public static List<Decl> curNextParamsDecls(List<Integer> prsIdx, List<String> prs) {
        List<Decl> o = new ArrayList<Decl>();
        if (!DashOptions.isElectrum) { o.add(curDecl()); o.add(nextDecl()); }
        o.addAll(paramDecls(prsIdx,  prs));
        return o;
    }

    public static Decl genEventDecl(int i) {
        if (i==0) return (Decl) new DeclExt(
                        DashStrings.genEventName + i,
                        createVar(DashStrings.allEventsName));
        else {
            List<String>cop = Collections.nCopies(i,DashStrings.identifierName);
            return (Decl) new DeclExt(
                        DashStrings.genEventName + i,
                        createArrowStringList(DashUtilFcns.newListWith(cop, DashStrings.allEventsName)));
        }
    }

    public static Decl scopeDecl(int i) {
        List<String>cop = Collections.nCopies(i,DashStrings.identifierName);
        return (Decl) new DeclExt(
                        DashStrings.scopeName + i,
                        createArrowStringList(DashUtilFcns.newListWith(cop, DashStrings.stateLabelName)));
    }

    // common vars
    // s
    public static ExprVar curVar() {
        return createVar(DashStrings.curName);
    }
    // s'
    public static ExprVar nextVar() {
        return createVar(DashStrings.nextName);
    }
    //[s,s']
    public static List<Expr> curNextVars() {
        List<Expr> o = new ArrayList<Expr>();
        o.add(curVar());
        o.add(nextVar());
        return o;        
    }
    //pi: Identfiers
    //public static Expr posParamVar(Integer i) {
    //    return createVar(DashStrings.pName+Integer.toString(i));
    //}
    // p0_AID
    public static Expr paramVar(Integer i, String n) {
        return createVar(DashStrings.pName+Integer.toString(i)+"_"+n);
    }
    // [p0_AID,p1_AID,...]
    public static List<Expr> paramVars(List<Integer> prsIdx, List<String> prs) {
        assert(prsIdx.size() == prs.size());
        List<Expr> o = new ArrayList<Expr>();
        for (int i=0;i<prsIdx.size();i++) o.add(paramVar(prsIdx.get(i),prs.get(i)));
        return o;
    }
    // [s, p1,p2,...]
    public static List<Expr> curParamVars(List<Integer> prsIdx, List<String> prs) {
        List<Expr> o = new ArrayList<Expr>();
        o.add(curVar());
        o.addAll(paramVars(prsIdx,prs));
        return o;
    }
    // [s', p1,p2,...]
    public static List<Expr> nextParamVars(List<Integer> prsIdx, List<String> prs) {
        List<Expr> o = new ArrayList<Expr>();
        o.add(nextVar());
        o.addAll(paramVars(prsIdx, prs));
        return o;
    }
    // [s,s',  p1,p2,...]
    public static List<Expr> curNextParamVars(List<Integer> prsIdx, List<String> prs) {
        List<Expr> o = new ArrayList<Expr>(curNextVars());
        o.addAll(paramVars(prsIdx,prs));
        return o;
    }

    // stable
    public static Expr stable() {
        return createVar(DashStrings.stableName);
    }

    public static Expr allInternalEventsVar() {
        return createVar(DashStrings.allInternalEventsName);
    }
    public static Expr allEnvironmentalEventsVar() {
        return createVar(DashStrings.allEnvironmentalEventsName);
    }

    public static Expr scopesUsedVar(int size) {
        return createVar(DashStrings.scopesUsedName + size);
    }
    public static Expr scopeVar(int size) {
        return createVar(DashStrings.scopeName + size);
    }
    public static Expr genEventVar(int size) {
        return createVar(DashStrings.genEventName + size);
    }
    public static Expr confVar(int size) {
        return createVar(DashStrings.confName + size);
    }
    public static Expr eventsVar(int size) {
        return createVar(DashStrings.eventsName + size);
    }

    public static Expr curScopesUsed(int size) {
        return curJoinExpr(scopesUsedVar(size));
    }
    // s'.scopesUsed5
    public static Expr nextScopesUsed(int size) {
        return nextJoinExpr(scopesUsedVar(size));
    }
    // s.conf4
    public static Expr curConf(int size) {
        return curJoinExpr(confVar(size));
    }
    // s'.conf3
    public static Expr nextConf(int size) {
        return nextJoinExpr(confVar(size));
    }
    // s.event4
    public static Expr curEvents(int size) {
        return curJoinExpr(eventsVar(size));
    }
    // s'.event3
    public static Expr nextEvents(int size) {
        return nextJoinExpr(eventsVar(size));
    }

    // s.stable == boolean/True
    public static Expr curStableTrue() {
        return createEquals(curJoinExpr(stable()),createTrue());
    }
   // s.stable == boolean/False
    public static Expr curStableFalse() {
        return createEquals(curJoinExpr(stable()),createFalse());
    }
    // s'.stable == boolean/True
    public static Expr nextStableTrue() {
        return createEquals(nextJoinExpr(stable()),createTrue());
    }
   // s'.stable == boolean/False
    public static Expr nextStableFalse() {
        return createEquals(nextJoinExpr(stable()),createFalse());
    }

    // s.name
    public static Expr curJoinExpr(Expr e) {
        return createJoin(curVar(), e);
    }
    //s'.name
    public static Expr nextJoinExpr(Expr e) {
        if (DashOptions.isElectrum) {
            //TODO -- prime all variables??
            return createTrue();
        } else {
            return createJoin(nextVar(), e);
        }
    }
    /*
    // p3 -> p2 -> p1 -> x
    public static Expr paramsToXArrow(List<Integer> prsIdx, List<String> prs, String x) {
        Collections.reverse(prsIdx);
        Expr e = createVar(x);
        for (int i=0;i<prsIdx.size();i++) {
            e = createArrow(paramVar(prsIdx.get(i),prs.get(i)),e);
        }
        return e;
    }
    */

    public static Expr translateDashRefToArrow(DashRef e) {
        List<Expr> ll = new ArrayList<Expr>(e.getParamValues());
        Collections.reverse(ll);
        ll.add(createVar(translateFQN(e.getName())));
        return createArrowExprList(ll);
    }

    public static Expr translateDashRefToJoin(DashRef e) {
        List<Expr> ll = new ArrayList<Expr>(e.getParamValues());
        Collections.reverse(ll);
        ll.add(createVar(translateFQN(e.getName())));
        return createJoinList(ll);
    }

    //TODO better name!
    public static boolean isWeirdOne(String vfqn, DashModule d) {
        //System.out.println("Vqn: " + vfqn);
        return d.getVarBufferParams(vfqn).size() == 0 && isExprArrow(d.getVarType(vfqn));
    }
    public static Expr translateExpr(Expr exp, DashModule d) {
        // special case for Variables.v1 if v1 has no params and has an 
        // arrow type  and isElectrum
        //System.out.println(exp);
        if (DashRef.isDashRef(exp)) {
            String vName = ((DashRef) exp).getName();
            // have to translate paramvalues
            // may be empty
            List<Expr> paramValuesList = 
                ((DashRef) exp).getParamValues().stream()
                    .map(i -> translateExpr(i,d))
                    .collect(Collectors.toList());

            //common subexpressions
            Boolean hasPrime = DashStrings.hasPrime(vName);
            Boolean isWeirdOne = isWeirdOne(DashStrings.removePrime(vName),d);
            Expr voutNotPrime = createVar(translateFQN(DashStrings.removePrime(vName)));
            Expr voutMayHavePrime;
            if (!hasPrime) voutMayHavePrime = voutNotPrime;
            else voutMayHavePrime = 
                createVar(translateFQN(DashStrings.removePrime(vName))+DashStrings.PRIME);

            //System.out.println(paramValuesList);
            if (DashOptions.isElectrum) {
                // already has prime or not
                if (isWeirdOne)
                    return createJoin(createVar(DashStrings.variablesName), voutMayHavePrime);
                else {
                    paramValuesList.add(voutMayHavePrime);
                    return createJoinList(paramValuesList);
                }
            } else {
                if (hasPrime) paramValuesList.add(nextJoinExpr(voutNotPrime));
                else paramValuesList.add(curJoinExpr(voutNotPrime));
                return createJoinList(paramValuesList);
            }

        } else if (isExprVar(exp)) {
            return exp;

        } else if (isExprBinary(exp)) {
            return ((ExprBinary) exp).op.make(
                exp.pos,
                exp.closingBracket,
                translateExpr(getLeft(exp),d),
                translateExpr(getRight(exp),d));

        } else if (isExprBadJoin(exp)) {
            return ExprBadJoin.make(
                exp.pos,
                exp.closingBracket,
                translateExpr(getLeft(exp),d),
                translateExpr(getRight(exp),d));

        } else if (exp instanceof ExprCall) {
            return ExprCall.make(
                exp.pos, 
                exp.closingBracket,
                ((ExprCall) exp).fun, 
                ((ExprCall) exp).args.stream()
                    .map(i -> translateExpr(i,d))
                    .collect(Collectors.toList()), 
                ((ExprCall) exp).extraWeight);

        } else if (exp instanceof ExprChoice){
            //TODO: check into this cast
            // not sure why is it necessary
            ConstList<Expr> x = (ConstList<Expr>) ((ExprChoice) exp).choices.stream()
                    .map(i -> translateExpr(i,d))
                    .collect(Collectors.toList());
            return ExprChoice.make(
                false,
                exp.pos, 
                x,
                ((ExprChoice) exp).reasons);

        } else if (exp instanceof ExprITE){
            return ExprITE.make(
                exp.pos,
                translateExpr(getCond(exp),d),
                translateExpr(getLeft(exp),d),
                translateExpr(getRight(exp),d));

        } else if (exp instanceof ExprList){
            return ExprList.make(
                exp.pos, 
                exp.closingBracket,
                ((ExprList) exp).op,
                ((ExprList) exp).args.stream()
                    .map(i -> translateExpr(i,d))
                    .collect(Collectors.toList())); 

        } else if (exp instanceof ExprUnary){
            return ((ExprUnary) exp).op.make(
                exp.pos,
                translateExpr(((ExprUnary) exp).sub,d));

        } else if (exp instanceof ExprLet){
            //TODO rule out var name
            return ExprLet.make(
                exp.pos, 
                ((ExprLet) exp).var, 
                translateExpr(((ExprLet) exp).expr,d),
                translateExpr(((ExprLet) exp).sub,d));

        } else if (exp instanceof ExprQt){

            // have to translate the expressions in the decls too
            List<Decl> decls = ((ExprQt) exp).decls.stream()
                .map(i -> new Decl(
                    i.isPrivate,
                    i.disjoint,
                    i.disjoint2,
                    i.isVar,
                    i.names,
                    translateExpr(i.expr, d)))
                .collect(Collectors.toList());
            return ((ExprQt) exp).op.make(
                exp.pos, 
                exp.closingBracket,  
                decls, 
                translateExpr(((ExprQt) exp).sub,d));

        } else if (exp instanceof ExprConstant){
            return exp;

        } else {
            DashErrors.UnsupportedExpr("translateExpr", exp);
            return null;
        }
    }

    public static Expr bufferIndexVar(int i) {
        return createVar(DashStrings.bufferIndexName + i);
    }
    // none -> none -> none
    public static Expr createNoneArrow(int i) {
        if (i==0) return createNone();
        else {
            //System.out.println(i);
            //System.out.println(Collections.nCopies(i+1,createNone()));
            return createArrowExprList(Collections.nCopies(i+1,createNone()));
        }
    }
    /*
    public static Expr predJoinCurParams(String name, List<String> prs) {
        //p2.p1.p0.s.name
        Expr e = createVar(name);
        List<Expr> prsVarList = convertParamsToVars(prs);
        if (!DashOptions.isElectrum) e = createJoin(curVar(),e);
        if (prs!= null) {
            Collections.reverse(prsVarList);
            prsVarList.add(e);
            System.out.println("predJoinCurParams: " +prsVarList);
            Expr x = createJoinList(prsVarList);
            System.out.println("Join of prsVarList: " + x);
            return createJoinList(prsVarList) ;
        } else return e;
    }
    public static Expr predJoinCurNextParams(String name, List<String> prs) {
        //p2.p1.p0.s'.s.pre_transName
        Expr e = createVar(name);
        List<Expr> prsVarList = convertParamsToVars(prs);
        if (!DashOptions.isElectrum) e = createJoin(nextVar(),createJoin(curVar(),e));
        if (prs!=null) {
            Collections.reverse(prsVarList);
            prsVarList.add(e);
            return createJoinList(prsVarList) ;
        } else return e;      
    }
    */
}
