package ca.uwaterloo.watform.dashtoalloy;

import java.util.Collections;
import java.util.stream.Collectors;
import java.util.List;
import java.util.ArrayList;
import java.util.Arrays;

import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Expr;

import ca.uwaterloo.watform.core.DashOptions;
import ca.uwaterloo.watform.core.DashStrings;
import ca.uwaterloo.watform.core.DashUtilFcns;
import ca.uwaterloo.watform.core.DashRef;

// shortens the code to import these statically
import static ca.uwaterloo.watform.core.DashFQN.*;
import static ca.uwaterloo.watform.alloyasthelper.ExprHelper.*;

import ca.uwaterloo.watform.alloyasthelper.DeclExt;
import ca.uwaterloo.watform.alloyasthelper.ExprToString;

import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.parser.CompModuleHelper;

public class Common {

    // common decls
    public static Decl curDecl() {
        return (Decl) new DeclExt(DashStrings.curName, DashStrings.snapshotName);
    }
    public static Decl nextDecl() {
        return (Decl) new DeclExt(DashStrings.nextName, DashStrings.snapshotName);
    }
    public static Decl paramDecl(String n) {
        return (Decl) new DeclExt(DashStrings.pName+n, n);
    }
    public static List<Decl> curNextDecls() {
        List<Decl> o = new ArrayList<Decl>();
        if (!DashOptions.isElectrum) {
            o.add(curDecl());
            o.add(nextDecl());
        }
        return o;
    }
    public static List<Decl> paramDecls(List<String> prs) {
        List<Decl> o = new ArrayList<Decl>();
        for (String n: prs) o.add(paramDecl(n));
        return o;
    }
    public static List<Decl> curParamsDecls(List<String> prs) {
        List<Decl> o = new ArrayList<Decl>();
        if (!DashOptions.isElectrum) o.add(curDecl());
        o.addAll(paramDecls(prs));
        return o;
    }
    public static List<Decl> curNextParamsDecls(List<String> prs) {
        List<Decl> o = new ArrayList<Decl>();
        if (!DashOptions.isElectrum) { o.add(curDecl()); o.add(nextDecl()); }
        o.addAll(paramDecls(prs));
        return o;
    }
    public static Decl eventsDecl(int i) {
        return (Decl) new DeclExt(DashStrings.eventsName + i, DashStrings.allEventsName);
    }
    public static Decl scopesUsedDecl(int i) {
        return (Decl) new DeclExt(DashStrings.scopesUsedName + i, DashStrings.stateLabelName);
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
    public static List<Expr> curNextVars() {
        List<Expr> o = new ArrayList<Expr>();
        o.add(curVar());
        o.add(nextVar());
        return o;        
    }
    // [n1,n2,...]
    public static List<Expr> paramVars(List<String> names) {
        List<Expr> o = new ArrayList<Expr>();
        for (String n: names) o.add(createVar(DashStrings.pName+n));
        return o;
    }
    public static List<Expr> curParamVars(List<String> params) {
        List<Expr> o = new ArrayList<Expr>();
        o.add(curVar());
        o.addAll(paramVars(params));
        return o;
    }
    public static List<Expr> curNextParamVars(List<String> params) {
        List<Expr> o = new ArrayList<Expr>(curNextVars());
        o.addAll(paramVars(params));
        return o;
    }

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
    // p3 -> p2 -> p1 -> x
    public static Expr paramsToXArrow(List<String> prs, String x) {
        Collections.reverse(prs);
        Expr e = createVar(x);
        for (String p: prs) {
            e = createArrow(createVar(p),e);
        }
        return e;
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
