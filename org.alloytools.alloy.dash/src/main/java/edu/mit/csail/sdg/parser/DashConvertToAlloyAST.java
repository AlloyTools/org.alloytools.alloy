package edu.mit.csail.sdg.parser;

import java.util.ArrayList;
import java.util.List;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Attr.AttrType;
import edu.mit.csail.sdg.ast.DashConcState;
import edu.mit.csail.sdg.ast.DashState;
import edu.mit.csail.sdg.ast.DashTrans;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBadJoin;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;

public class DashConvertToAlloyAST {

    public static void convertToAlloyAST(DashModule module) {
        //createSnapshotSigAST(module);
        printTransitions(module);

    }

    static void addSigAST(DashModule module, String sigName, ExprVar isExtends, List<ExprVar> sigParent, List<Decl> decls, Pos isAbstract, Pos isLone, Pos isOne, Pos isSome, Pos isPrivate) {
        module.addSig(sigName, isExtends, sigParent, decls, null, null, AttrType.ABSTRACT.makenull(isAbstract), AttrType.LONE.makenull(isLone), AttrType.ONE.makenull(isOne), AttrType.SOME.makenull(isSome), AttrType.PRIVATE.makenull(isPrivate));

    }

    static void printTransitions(DashModule module) {
        for (DashTrans transition : module.transitions.values()) {
            printPreCondition(transition, module, false);
        }
    }

    /*
     * Taken from the Dash.cup file. It is used for handling difficult parsing
     * ambiguities with Alloy expressions
     */
    private static Expr mult(Expr x) throws Err {
        if (x instanceof ExprUnary) {
            ExprUnary y = (ExprUnary) x;
            if (y.op == ExprUnary.Op.SOME)
                return ExprUnary.Op.SOMEOF.make(y.pos, y.sub);
            if (y.op == ExprUnary.Op.LONE)
                return ExprUnary.Op.LONEOF.make(y.pos, y.sub);
            if (y.op == ExprUnary.Op.ONE)
                return ExprUnary.Op.ONEOF.make(y.pos, y.sub);
        }
        return x;
    }

    static void createSnapshotSigAST(DashModule module) {
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();

        //Create AST for variable declaration:
        //stable: one Bool
        if (module.stateHierarchy) {
            Expr b = ExprUnary.Op.ONE.make(null, ExprVar.make(null, "Bool"));
            a.add(ExprVar.make(null, "stable"));
            decls.add(new Decl(null, null, null, null, a, mult(b)));
            a.clear();
        }

        for (String variableName : module.envVariable2Expression.keySet()) {
            Expr b = module.envVariable2Expression.get(variableName);
            a.add(ExprVar.make(null, variableName));
            decls.add(new Decl(null, null, null, null, a, mult(b)));
            a.clear();
        }

        for (String variableName : module.variable2Expression.keySet()) {
            Expr b = module.variable2Expression.get(variableName);
            a.add(ExprVar.make(null, variableName));
            decls.add(new Decl(null, null, null, null, a, mult(b)));
            a.clear();
        }

        List<ExprVar> sigParent = new ArrayList<ExprVar>();
        sigParent.add(ExprVar.make(null, "BaseSnapshot"));
        addSigAST(module, "Snapshot", ExprVar.make(null, "extends"), sigParent, decls, new Pos("abstract", 0, 0), null, null, null, null);
    }

    static void printPreCondition(DashTrans transition, DashModule module, Boolean onlyExpr) {
        //We only want to print the expressions and not the pred name
        //if (!onlyExpr)
        //alloyModel += ("pred pre_" + transition.modifiedName + "[s: Snapshot]" + '\n');

        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        Expr b = ExprUnary.Op.ONE.make(null, ExprVar.make(null, "Snapshot"));
        a.add(ExprVar.make(null, "s"));
        decls.add(new Decl(null, null, null, null, a, mult(b))); //[s: Snapshot]

        Expr binaryFrom = null;
        //sourceState in s.conf
        if (transition.fromExpr.fromExpr.size() > 0) {
            Expr left = ExprVar.make(null, transition.fromExpr.fromExpr.get(0).replace('/', '_'));
            Expr right = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "conf"));
            binaryFrom = ExprBinary.Op.IN.make(null, null, left, right);
        }

        Expr binaryOn = null;
        // onExprName in (s.events & EnvironmentEvent)
        if (transition.onExpr.name != null) {
            Expr left = ExprVar.make(null, transition.onExpr.name.replace('/', '_'));
            Expr rightJoin = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "events")); // s.events
            Expr rightBinary = ExprBinary.Op.INTERSECT.make(null, null, rightJoin, ExprVar.make(null, "EnvironmentEvent")); // s.events & EnvironmentEvent
            binaryOn = ExprBinary.Op.IN.make(null, null, left, rightBinary); //onExprName in (s.events & EnvironmentEvent)
        }

        if (binaryOn != null)
            System.out.println("On Expr: " + binaryOn.toString());
        if (transition.whenExpr != null && transition.whenExpr.exprList != null) {
            for (Expr expr : transition.whenExpr.exprList) {
                getVarFromParentExpr(expr, getParentConcState(transition.parentState), module);
            }
        }


        if (transition.whenExpr != null) {
            for (Expr expr : transition.whenExpr.exprList) {
                System.out.println("When Expr: " + expr);
                //System.out.println("Expr: " + expr.toString() + " type: " + expr.getClass());
                //System.out.println("Expr Right: " + ((ExprBinary) expr).right + " type: " + ((ExprBinary) expr).right.getClass());
                //ExprBinary binRight = (ExprBinary) ((ExprBinary) expr).right;
                //System.out.println("Expr Right Right: " + binRight.right + " type: " + ((ExprBinary) expr).right.getClass());
                //System.out.println("Expr Right Left: " + binRight.left + " type: " + ((ExprBinary) expr).right.getClass());
            }
        }

        System.out.println("\n");

        ExprVar leftConf = ExprVar.make(null, "s.Elevator_conf");
        ExprVar rightConf = ExprVar.make(null, "s.Elevator_conf");
        ExprVar direction = ExprVar.make(null, "s.Elevator_direction");
        ExprVar called = ExprVar.make(null, "s.Elevator_called");

        Expr ExprBinConfDir = ExprBinary.Op.PLUS.make(null, null, rightConf, direction);
        Expr ExprRight = ExprBinary.Op.MINUS.make(null, null, ExprBinConfDir, called);
        Expr expr = ExprBinary.Op.EQUALS.make(null, null, leftConf, ExprRight);
        System.out.println("User Gen Expr: " + expr.toString());

        System.out.println("User Expr: " + expr.toString() + " type: " + expr.getClass());
        System.out.println("User Expr Right: " + ((ExprBinary) expr).right + " type: " + ((ExprBinary) expr).right.getClass());
        ExprBinary binRight = (ExprBinary) ((ExprBinary) expr).right;
        System.out.println("User Expr Right Right: " + binRight.right + " type: " + ((ExprBinary) expr).right.getClass());
        System.out.println("User Expr Right Left: " + binRight.left + " type: " + ((ExprBinary) expr).right.getClass());

        System.out.println("\n\n\n\n\n");
    }

    //Take an expression in a do statement and modify any variables present. Eg: active_players should become
    //s.Game_active_players (Given that active_players is declared under the Game concurrent state)
    static Expr modifyExprVar(Expr expr, DashConcState parent, DashModule module) {
        final List<String> variablesInParent = module.variableNames.get(parent.modifiedName);
        final List<String> envVariablesInParent = module.envVariableNames.get(parent.modifiedName);

        Expr expression = expr;

        DashConcState outerConcState = parent.parent;

        if (variablesInParent != null)
            expression = modifyExpr(expression, parent, expr, variablesInParent);
        if (envVariablesInParent != null)
            expression = modifyExpr(expression, parent, expr, envVariablesInParent);

        while (outerConcState != null) {
            if (module.variableNames.get(outerConcState.modifiedName) != null)
                expression = modifyExpr(expression, outerConcState, expr, module.variableNames.get(outerConcState.modifiedName));
            if (module.envVariableNames.get(parent.modifiedName) != null)
                expression = modifyExpr(expression, outerConcState, expr, module.envVariableNames.get(parent.modifiedName));
            outerConcState = outerConcState.parent;
        }

        return expression;
    }

    static Expr modifyExpr(Expr expression, DashConcState parent, Expr expr, List<String> exprList) {
        for (String var : exprList) {
            if (expr.toString().equals(var + "'"))
                return ExprBadJoin.make(null, null, ExprVar.make(null, "s'"), ExprVar.make(null, parent.modifiedName + '_' + var));
            else if (expr.toString().equals(var)) {
                return ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, parent.modifiedName + '_' + var));
            }
        }
        return expression;
    }

    private static void getVarFromParentExpr(Object parentExpr, DashConcState parent, DashModule module) {
        if (parentExpr instanceof ExprBinary) {
            ExprBinary exprBinary = (ExprBinary) parentExpr;
            getVarFromBinary(exprBinary, parent, module);
        }

        if (parentExpr instanceof ExprUnary) {
            ExprUnary unary = (ExprUnary) parentExpr;
            getVarFromUnary(unary, parent, module);
        }

        if (parentExpr instanceof ExprQt) {
            getVarFromExprQt((ExprQt) parentExpr, parent, module);
        }

        if (parentExpr instanceof ExprVar) {
            parentExpr = modifyExprVar((ExprVar) parentExpr, parent, module);
        }
    }

    /*
     * Breakdown a binary expression into its subcomponents Example of a binary
     * expression: #varible1 = #variable2
     */
    private static void getVarFromBinary(ExprBinary binary, DashConcState parent, DashModule module) {
        if (binary.left instanceof ExprUnary) {
            ExprUnary unary = (ExprUnary) binary.left;
            getVarFromUnary(unary, parent, module);
        }

        if (binary.left instanceof ExprVar) {
            (binary.left) = modifyExprVar(binary.left, parent, module);
        }

        if (binary.left instanceof ExprBinary) {
            getVarFromBinary((ExprBinary) binary.left, parent, module);
        }

        if (binary.left instanceof ExprBadJoin) {
            getVarFromBadJoin((ExprBadJoin) binary.left, parent, module);
        }

        if (binary.right instanceof ExprUnary) {
            ExprUnary unary = (ExprUnary) binary.right;
            getVarFromUnary(unary, parent, module);
        }

        if (binary.right instanceof ExprVar) {
            (binary.right) = modifyExprVar(binary.right, parent, module);
        }

        if (binary.right instanceof ExprBinary) {
            getVarFromBinary((ExprBinary) binary.right, parent, module);
        }

        if (binary.right instanceof ExprBadJoin) {
            getVarFromBadJoin((ExprBadJoin) binary.right, parent, module);
        }
    }

    /*
     * Breakdown a unary expression into its subcomponents Example of an unary
     * expression: one varible
     */
    private static String getVarFromUnary(ExprUnary unary, DashConcState parent, DashModule module) {
        if (unary.sub instanceof ExprVar) {
            unary.sub = modifyExprVar(unary.sub, parent, module);
        }
        if (unary.sub instanceof ExprUnary) {
            getVarFromUnary((ExprUnary) unary.sub, parent, module);
        }
        if (unary.sub instanceof ExprBadJoin) {
            getVarFromBadJoin((ExprBadJoin) unary.sub, parent, module);
        }
        if (unary.sub instanceof ExprBinary) {
            getVarFromBinary((ExprBinary) unary.sub, parent, module);
        }
        return null;
    }

    private static void getVarFromBadJoin(ExprBadJoin joinExpr, DashConcState parent, DashModule module) {
        if (joinExpr.left instanceof ExprVar) {
            //joinExpr.left = ExprVar.make(null, "Changed");
            joinExpr.left = modifyExprVar(joinExpr.left, parent, module);
        }
        if (joinExpr.left instanceof ExprUnary) {
            getVarFromUnary((ExprUnary) joinExpr.left, parent, module);
        }
        if (joinExpr.left instanceof ExprBadJoin) {
            getVarFromBadJoin((ExprBadJoin) joinExpr.right, parent, module);
        }
        if (joinExpr.right instanceof ExprVar) {
            joinExpr.right = modifyExprVar(joinExpr.right, parent, module);
        }
        if (joinExpr.right instanceof ExprUnary) {
            getVarFromUnary((ExprUnary) joinExpr.left, parent, module);
        }
        if (joinExpr.right instanceof ExprBadJoin) {
            getVarFromBadJoin((ExprBadJoin) joinExpr.right, parent, module);
        }
    }

    /*
     * Breakdown a quantified expression into its subcomponents
     */
    private static void getVarFromExprQt(ExprQt exprQt, DashConcState parent, DashModule module) {
        getDeclsFromExprQT(exprQt, parent, module);

        if (exprQt.sub instanceof ExprUnary) {
            getVarFromUnary((ExprUnary) exprQt.sub, parent, module);
        }
        if (exprQt.sub instanceof ExprBinary) {
            getVarFromBinary((ExprBinary) exprQt.sub, parent, module);
        }
        if (exprQt.sub instanceof ExprVar) {
            exprQt.sub = modifyExprVar(exprQt.sub, parent, module);
        }
    }

    private static void getDeclsFromExprQT(ExprQt exprQt, DashConcState parent, DashModule module) {
        for (Decl decl : exprQt.decls) {
            getVarFromParentExpr(decl.expr, parent, module);
        }
    }

    //Retrive the concurrent state inside which "item" is located
    static DashConcState getParentConcState(Object item) {
        if (item instanceof DashState) {
            if (((DashState) item).parent instanceof DashState)
                getParentConcState(((DashState) item).parent);
            if (((DashState) item).parent instanceof DashConcState)
                return (DashConcState) ((DashState) item).parent;
        }

        if (item instanceof DashConcState)
            return (DashConcState) item;

        return null;
    }

    public static void convertExpr() {
        Expr leftConf = ExprVar.make(null, "conf");
        Expr lefts = ExprVar.make(null, "s");
        Expr joined = ExprBadJoin.make(null, null, lefts, leftConf);

        Expr leftConfPrime = ExprVar.make(null, "conf");
        Expr leftSPrime = ExprVar.make(null, "s");
        Expr joinedPrime = ExprBadJoin.make(null, null, lefts, leftConf);

        Expr unary = ExprUnary.Op.NO.make(null, joined);
        Expr unaryPrime = ExprUnary.Op.NO.make(null, joined);
        Expr joinedExpr = ExprBinary.Op.AND.make(null, null, unary, unaryPrime);
    }
}
