package edu.mit.csail.sdg.parser;

import java.util.ArrayList;
import java.util.List;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Attr.AttrType;
import edu.mit.csail.sdg.ast.DashConcState;
import edu.mit.csail.sdg.ast.DashInit;
import edu.mit.csail.sdg.ast.DashState;
import edu.mit.csail.sdg.ast.DashTrans;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBadJoin;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprITE;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;

public class DashConvertToAlloyAST {

    public static void convertToAlloyAST(DashModule module) {
        createSnapshotSigAST(module);
        createTransitionsAST(module);
    }

    static void addSigAST(DashModule module, String sigName, ExprVar isExtends, List<ExprVar> sigParent, List<Decl> decls, Pos isAbstract, Pos isLone, Pos isOne, Pos isSome, Pos isPrivate) {
        module.addSig(sigName, isExtends, sigParent, decls, null, null, AttrType.ABSTRACT.makenull(isAbstract), AttrType.LONE.makenull(isLone), AttrType.ONE.makenull(isOne), AttrType.SOME.makenull(isSome), AttrType.PRIVATE.makenull(isPrivate));

    }

    static void createTransitionsAST(DashModule module) {
        for (DashTrans transition : module.transitions.values()) {
            //createPreConditionAST(transition, module, false);
            //createPostConditionAST(transition, module, false);
            //createSemanticsAST(transition, module, false);
            //createTransCallAST(transition, module, false);
        }
    }

    static void testORExpr() {

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

    /*
     * This function creates the AST for the Snapshot signature in the Alloy model
     */
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

        /* Creating the following expression: evnVar: mappings */
        for (String variableName : module.envVariable2Expression.keySet()) {
            Expr b = module.envVariable2Expression.get(variableName);
            a.add(ExprVar.make(null, variableName));
            decls.add(new Decl(null, null, null, null, a, mult(b)));
            a.clear();
        }

        /* Creating the following expression: variable: mappings */
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


    /*
     * This function creates the AST for the precondition predicate in the Alloy
     * Model
     */
    static void createPreConditionAST(DashTrans transition, DashModule module) {
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        Expr b = ExprUnary.Op.ONE.make(null, ExprVar.make(null, "Snapshot"));
        a.add(ExprVar.make(null, "s"));
        decls.add(new Decl(null, null, null, null, a, mult(b))); //[s: Snapshot]

        Expr expression = null; //This is the final expression that will be stored in the predicate AST

        Expr binaryFrom = null;
        /* Creating the following expression: sourceState in s.conf */
        if (transition.fromExpr.fromExpr.size() > 0) {
            Expr left = ExprVar.make(null, transition.fromExpr.fromExpr.get(0).replace('/', '_'));
            Expr right = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "conf"));
            binaryFrom = ExprBinary.Op.IN.make(null, null, left, mult(right));
        }

        /*
         * Creating the following expression: onExprName in (s.events &
         * EnvironmentEvent)
         */
        Expr binaryOn = null;
        if (transition.onExpr.name != null) {
            Expr left = ExprVar.make(null, transition.onExpr.name.replace('/', '_'));
            Expr rightJoin = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "events")); // s.events
            Expr rightBinary = ExprBinary.Op.INTERSECT.make(null, null, rightJoin, ExprVar.make(null, "EnvironmentEvent")); // s.events & EnvironmentEvent
            binaryOn = ExprBinary.Op.IN.make(null, null, left, mult(rightBinary)); //onExprName in (s.events & EnvironmentEvent)         
        }

        if (binaryOn != null)
            expression = ExprBinary.Op.AND.make(null, null, binaryFrom, binaryOn);


        /* Creating the following expression: AND[whenExpr, whenExpr, ..] */
        if (transition.whenExpr != null && transition.whenExpr.exprList != null) {
            for (Expr expr : transition.whenExpr.exprList) {
                getVarFromParentExpr(expr, getParentConcState(transition.parentState), module);
                if (expression == null)
                    expression = ExprBinary.Op.AND.make(null, null, binaryFrom, expr);
                else
                    expression = ExprBinary.Op.AND.make(null, null, expression, expr);
            }
        }

        expression = ExprUnary.Op.NOOP.make(null, expression);
        module.addFunc(null, null, "pre_" + transition.modifiedName, null, decls, null, expression);
    }

    /*
     * This function creates the AST for the postcondition predicate in the Alloy
     * Model
     */
    static void createPostConditionAST(DashTrans transition, DashModule module) {
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        Expr b = ExprUnary.Op.ONE.make(null, ExprVar.make(null, "Snapshot")); //LOOK INTO THIS AGAIN. DOES NOT APPEAR CORRECT
        a.add(ExprVar.make(null, "s"));
        a.add(ExprVar.make(null, "s'"));
        decls.add(new Decl(null, null, null, null, a, mult(b))); //[s, s': Snapshot]

        Expr expression = null;

        Expr binaryGoTo = null;
        /*
         * Creating the following expression: s'.conf = s.conf - sourceState +
         * destinationState
         */
        if (transition.gotoExpr.gotoExpr.size() > 0) {
            Expr gotoExpr = ExprVar.make(null, transition.gotoExpr.gotoExpr.get(0).replace('/', '_'));
            Expr fromExpr = ExprVar.make(null, transition.fromExpr.fromExpr.get(0).replace('/', '_'));
            Expr sConf = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "conf"));
            Expr sConfPrime = ExprBadJoin.make(null, null, ExprVar.make(null, "s'"), ExprVar.make(null, "conf"));
            Expr binaryRight = ExprBinary.Op.PLUS.make(null, null, ExprBinary.Op.MINUS.make(null, null, sConf, fromExpr), gotoExpr);
        }

        /* Creating the following expression: no (s'.events & EnvironmentEvent) */
        Expr sendExpr = null;
        if (transition.sendExpr == null && DashOptions.isEnvEventModel) {
            Expr join = ExprBadJoin.make(null, null, ExprVar.make(null, "s'"), ExprVar.make(null, "events")); // s'.events
            Expr rightBinary = ExprBinary.Op.INTERSECT.make(null, null, join, ExprVar.make(null, "InternalEvent")); // s'.events & EnvironmentEvent
            sendExpr = ExprUnary.Op.NO.make(null, rightBinary); // no (s'.events & EnvironmentEvent)
        }
        /* Creating the following expression: sentEvent in s'.events */
        else if (transition.sendExpr != null && transition.sendExpr.name != null) {
            Expr join = ExprBadJoin.make(null, null, ExprVar.make(null, "s'"), ExprVar.make(null, "events")); // s'.events
            sendExpr = ExprBinary.Op.IN.make(null, null, ExprVar.make(null, transition.sendExpr.name), mult(join)); // sentEvent in s'.events
        }

        if (sendExpr != null)
            expression = ExprBinary.Op.AND.make(null, null, binaryGoTo, sendExpr);

        /* Creating the following expression: AND[doexpr, doexpr, ..] */
        if (transition.doExpr != null && transition.doExpr.exprList != null) {
            for (Expr expr : transition.doExpr.exprList) {
                getVarFromParentExpr(expr, getParentConcState(transition.parentState), module);
                if (expression == null)
                    expression = ExprBinary.Op.AND.make(null, null, binaryGoTo, expr);
                else
                    expression = ExprBinary.Op.AND.make(null, null, expression, expr);
            }
            //These are the variables that have not been changed in the post-cond and they need to retain their values in the next snapshot
            for (String var : getUnchangedVars(transition.doExpr.exprList, getParentConcState(transition.parentState), module)) {
                Expr binaryLeft = ExprBadJoin.make(null, null, ExprVar.make(null, "s'"), ExprVar.make(null, getParentConcState(transition.parentState).modifiedName + "_" + var)); //s'.variableParent_varName
                Expr binaryRight = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, getParentConcState(transition.parentState).modifiedName + "_" + var)); //s'.variableParent_varName
                Expr binaryEquals = ExprBinary.Op.EQUALS.make(null, null, binaryLeft, binaryRight);
                expression = ExprBinary.Op.AND.make(null, null, expression, binaryEquals);
            }
        }

        /* Creating the following expression: s'.variable = s.variable */
        if (transition.doExpr == null) {
            //These are the variables that have not been changed in the post-cond and they need to retain their values in the next snapshot
            for (String var : getUnchangedVars(transition.doExpr.exprList, getParentConcState(transition.parentState), module)) {
                Expr binaryLeft = ExprBadJoin.make(null, null, ExprVar.make(null, "s'"), ExprVar.make(null, getParentConcState(transition.parentState).modifiedName + "_" + var)); //s'.variableParent_varName
                Expr binaryRight = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, getParentConcState(transition.parentState).modifiedName + "_" + var)); //s'.variableParent_varName
                Expr binaryEquals = ExprBinary.Op.EQUALS.make(null, null, binaryLeft, binaryRight);
                expression = ExprBinary.Op.AND.make(null, null, expression, binaryEquals);
            }
        }

        expression = ExprUnary.Op.NOOP.make(null, expression);
        module.addFunc(null, null, "post_" + transition.modifiedName, null, decls, null, expression);
    }

    /*
     * This function creates the AST for the Semantics predicate in the Alloy Model
     */
    static void createSemanticsAST(DashTrans transition, DashModule module) {
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        Expr b = ExprUnary.Op.ONE.make(null, ExprVar.make(null, "Snapshot"));
        a.add(ExprVar.make(null, "s"));
        a.add(ExprVar.make(null, "s'"));
        decls.add(new Decl(null, null, null, null, a, mult(b))); //[s, s': Snapshot]

        Expr expression = null;

        /* Creating the following expression: s'.taken = currentTrans */
        Expr semanticsExpr = null;
        Expr sTakenPrime = ExprBadJoin.make(null, null, ExprVar.make(null, "s'"), ExprVar.make(null, "taken")); //s'.taken
        if (!module.stateHierarchy) {
            semanticsExpr = ExprBinary.Op.EQUALS.make(null, null, sTakenPrime, ExprVar.make(null, transition.modifiedName)); //s'.taken = currentTrans
            expression = semanticsExpr;
        }

        /*
         * Creating the following expression: s.stable = True => (s'.taken + transName)
         * else { no (s'.taken + t) & (AND[transitions])
         */
        Expr ifElseExpr = null;
        if (module.stateHierarchy) {
            Expr ifCond = ExprBinary.Op.EQUALS.make(null, null, ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "stable")), ExprVar.make(null, "True")); //s.stable = True
            Expr ifExpr = ExprBinary.Op.EQUALS.make(null, null, sTakenPrime, ExprVar.make(null, transition.modifiedName)); //s'.taken = currentTrans
            Expr ElseExprLeft = ExprUnary.Op.NO.make(null, ExprBinary.Op.PLUS.make(null, null, sTakenPrime, ExprVar.make(null, "t"))); //no (s'.taken + t)
            Expr ElseExprRight = null;
            for (DashTrans trans : module.transitions.values()) {
                if (getParentConcState(trans.parentState).modifiedName.equals(getParentConcState(transition.parentState).modifiedName)) {
                    if (ElseExprRight == null)
                        ElseExprRight = ExprVar.make(null, trans.modifiedName);
                    else
                        ElseExprRight = ExprBinary.Op.OR.make(null, null, ElseExprRight, ExprVar.make(null, trans.modifiedName));
                }
            }
            Expr ElseExpr = ExprBinary.Op.AND.make(null, null, ElseExprLeft, ElseExprRight);
            ifElseExpr = ExprITE.make(null, ifCond, ifExpr, ElseExpr);
            expression = ifElseExpr;
        }

        expression = ExprUnary.Op.NOOP.make(null, expression);
        module.addFunc(null, null, "semantics_" + transition.modifiedName, null, decls, null, expression);
    }

    /*
     * This function creates the AST for the transition call (the one that refers to
     * the pre,post,semantics) predicate in the Alloy Model
     */
    static void createTransCallAST(DashTrans transition, DashModule module) {
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        Expr b = ExprUnary.Op.ONE.make(null, ExprVar.make(null, "Snapshot"));
        a.add(ExprVar.make(null, "s"));
        a.add(ExprVar.make(null, "s'"));
        decls.add(new Decl(null, null, null, null, a, mult(b))); //[s, s': Snapshot]

        Expr ssprimeJoin = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "s"));

        /*
         * Creating the following expressions: post_transName[s, s'],
         * semantics_transName[s, s'], pre_transName[s]
         */
        Expr predCallExpr = ExprBadJoin.make(null, null, ssprimeJoin, ExprVar.make(null, "post_" + transition.modifiedName)); //s.s'.post_transName
        predCallExpr = ExprBinary.Op.AND.make(null, null, predCallExpr, ExprBadJoin.make(null, null, ssprimeJoin, ExprVar.make(null, "semantics_" + transition.modifiedName))); //s.s'.post_transName
        predCallExpr = ExprBinary.Op.AND.make(null, null, predCallExpr, ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "semantics_" + transition.modifiedName))); //s.post_transName

        predCallExpr = ExprUnary.Op.NOOP.make(null, predCallExpr);
        module.addFunc(null, null, transition.modifiedName, null, decls, null, predCallExpr);
    }

    /*
     * This function creates an AST for the following predicate: pred
     * enabledAfterStep_transName[_s, s: Snapshot] {expressions}
     */
    static void createEnabledNextStepAST(DashTrans transition, DashModule module) {
        Expr expr = null;
        if (module.stateHierarchy) {
            Expr ifCond = ExprBinary.Op.EQUALS.make(null, null, ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "stable")), ExprVar.make(null, "True")); //s.stable = True
            Expr ifExprLeft = ExprUnary.Op.NO.make(null, ExprVar.make(null, "t"));
            Expr ifExprRight = null;
            for (DashTrans trans : module.transitions.values()) {
                if (getParentConcState(trans.parentState).modifiedName.equals(getParentConcState(transition.parentState).modifiedName)) {
                    if (ifExprRight == null)
                        ifExprRight = ExprVar.make(null, trans.modifiedName);
                    else
                        ifExprRight = ExprBinary.Op.OR.make(null, null, ifExprRight, ExprVar.make(null, trans.modifiedName));
                }
            }
            Expr ifExpr = ExprBinary.Op.AND.make(null, null, ifExprLeft, ifExprRight);

            Expr elseExpr = null;
            Expr elseExprLeft = ExprUnary.Op.NO.make(null, ExprBinary.Op.PLUS.make(null, null, ExprBadJoin.make(null, null, ExprVar.make(null, "_s"), ExprVar.make(null, "taken")), ExprVar.make(null, "t")));
            Expr elseExprRight = null;
            for (DashTrans trans : module.transitions.values()) {
                if (getParentConcState(trans.parentState).modifiedName.equals(getParentConcState(transition.parentState).modifiedName)) {
                    if (elseExprRight == null)
                        elseExprRight = ExprVar.make(null, trans.modifiedName);
                    else
                        elseExprRight = ExprBinary.Op.OR.make(null, null, elseExprRight, ExprVar.make(null, trans.modifiedName));
                }
            }
            elseExpr = ExprBinary.Op.AND.make(null, null, elseExprLeft, elseExprRight);
            expr = ExprITE.make(null, ifCond, ifExpr, elseExpr);
        }
    }

    /*
     * This function creates an AST for the following predicate: pred small_step[s,
     * s': Snapshot] { operation[s, s'] }
     */
    static void createSmallStepAST(DashTrans transition, DashModule module) {
        Expr sSPrime = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "s'"));
        Expr operationCall = ExprBadJoin.make(null, null, sSPrime, ExprVar.make(null, "operation"));
    }

    /*
     * This function creates an AST for the facts in the Model Definition
     */
    static void createModelDefFact(DashTrans transition, DashModule module) {
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        Expr snapshot = ExprUnary.Op.ONE.make(null, ExprVar.make(null, "Snapshot"));
        Expr s = ExprVar.make(null, "s");
        Expr sPrime = ExprVar.make(null, "s'");
        Expr ssPrime = ExprBadJoin.make(null, null, s, sPrime);

        /*
         * Creating the following expression: all s: Snapshot | s in initial iff init[s]
         */
        a.add((ExprVar) s);
        decls.add(new Decl(null, null, null, null, a, mult(snapshot))); //s: Snapshot
        Expr rightQT = ExprBinary.Op.IFF.make(null, null, ExprBinary.Op.IN.make(null, null, s, ExprVar.make(null, "initial")), ExprBadJoin.make(null, null, s, ExprVar.make(null, "init")));
        Expr expr = ExprQt.Op.ALL.make(null, null, decls, rightQT); //all s: Snapshot | s in initial iff init[s]
        a.clear();
        decls.clear();

        /*
         * Creating the following expression: all s: Snapshot | s in nextStep iff
         * small_step[s, s']
         */
        a.add((ExprVar) s);
        a.add((ExprVar) sPrime);
        decls.add(new Decl(null, null, null, null, a, mult(snapshot))); //s, s': Snapshot
        rightQT = ExprBinary.Op.IFF.make(null, null, ExprBinary.Op.IN.make(null, null, s, ExprVar.make(null, "nextStep")), ExprBadJoin.make(null, null, ssPrime, ExprVar.make(null, "small_step")));
        expr = ExprQt.Op.ALL.make(null, null, decls, rightQT); //all s: Snapshot | s in nextStep iff small_step[s, s']

        /*
         * Creating the following expression: all s, s': Snapshot | s->s' in nextStep
         * iff small_step[s, s']
         */
        Expr sArrowSPrime = ExprBinary.Op.ARROW.make(null, null, s, sPrime);
        rightQT = ExprBinary.Op.IFF.make(null, null, ExprBinary.Op.IN.make(null, null, sArrowSPrime, ExprVar.make(null, "nextStep")), ExprBadJoin.make(null, null, ssPrime, ExprVar.make(null, "small_step")));
        expr = ExprQt.Op.ALL.make(null, null, decls, rightQT); //all s, s': Snapshot | s->s' in nextStep iff small_step[s, s']

        /*
         * Creating the following expression: /all s, s': Snapshot | equals[s, s'] => s
         * = s'
         */
        rightQT = ExprBinary.Op.IFF.make(null, null, ExprBadJoin.make(null, null, sArrowSPrime, ExprVar.make(null, "equals")), ExprBinary.Op.EQUALS.make(null, null, s, sPrime));
        expr = ExprQt.Op.ALL.make(null, null, decls, rightQT); //all s, s': Snapshot | equals[s, s'] => s = s'
        a.clear();
        decls.clear();

        /*
         * Creating the following expression: all s': Snapshot | (isEnabled[s] && no s':
         * Snapshot | small_step[s, s']) => s.stable = False
         */
        Expr isEnabledCall = ExprBadJoin.make(null, null, s, ExprVar.make(null, "isEnabled"));
        a.add((ExprVar) sPrime);
        decls.add(new Decl(null, null, null, null, a, mult(snapshot))); //s': Snapshot
        Expr qtExpr = ExprQt.Op.NO.make(null, null, decls, ExprBadJoin.make(null, null, ssPrime, ExprVar.make(null, "small_step")));// no s': Snapshot | small_step[s, s']
        Expr iffLeft = ExprBinary.Op.INTERSECT.make(null, null, isEnabledCall, qtExpr);
        Expr iffRight = ExprBinary.Op.EQUALS.make(null, null, ExprBadJoin.make(null, null, s, ExprVar.make(null, "stable")), ExprVar.make(null, "False")); //s.stable = False
        Expr iffExpr = ExprBinary.Op.IFF.make(null, null, iffLeft, iffRight); //(isEnabled[s] && no s': Snapshot | small_step[s, s']) => s.stable = False
        a.clear();
        decls.clear();
        a.add((ExprVar) s);
        decls.add(new Decl(null, null, null, null, a, mult(snapshot))); //s: Snapshot
        expr = ExprQt.Op.ALL.make(null, null, decls, iffExpr);//all s': Snapshot | (isEnabled[s] && no s': Snapshot | small_step[s, s']) => s.stable = False


        /*
         * Creating the following expression: all s: Snapshot | s.stable = False => some
         * s.nextStep
         */
        iffLeft = ExprBinary.Op.EQUALS.make(null, null, ExprBadJoin.make(null, null, s, ExprVar.make(null, "stable")), ExprVar.make(null, "False")); //s.stable = False
        iffRight = ExprUnary.Op.SOME.make(null, ExprBadJoin.make(null, null, s, ExprVar.make(null, "nextStep")));
        iffExpr = ExprBinary.Op.IFF.make(null, null, iffLeft, iffRight);
        expr = ExprQt.Op.ALL.make(null, null, decls, iffExpr);

    }

    /*
     * This function creates an AST for the following predicate: pred operation[s,
     * s': Snapshot] { expressions }
     */
    static void createOperationAST(DashTrans transition, DashModule module) {
        Expr sSPrime = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "s'"));
        Expr expr = null;

        for (String key : module.transitions.keySet()) {
            if (expr == null)
                expr = ExprBadJoin.make(null, null, sSPrime, ExprVar.make(null, key));
            else
                expr = ExprBinary.Op.OR.make(null, null, expr, ExprBadJoin.make(null, null, sSPrime, ExprVar.make(null, key)));
        }
    }

    /*
     * This function creates an AST for the following predicate: pred
     * testIfNextStable[s, s': Snapshot, genEvents: set InternalEvent,
     * t:TransitionLabel] {}
     */
    static void createTestIfStableAST(DashTrans transition, DashModule module) {
        Expr sSPrime = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "s'")); //[s, s']
        Expr sSPrimeGenEvn = ExprBadJoin.make(null, null, sSPrime, ExprVar.make(null, "genEvents")); //[s, s', genEvents]
        Expr sSPrimeGenEvnt = ExprBadJoin.make(null, null, sSPrimeGenEvn, ExprVar.make(null, "t")); //[s, s', genEvents, t]
        Expr expr = null;

        for (String key : module.transitions.keySet()) {
            if (expr == null)
                expr = ExprUnary.Op.NOT.make(null, ExprBadJoin.make(null, null, sSPrimeGenEvnt, ExprVar.make(null, "enabledAfterStep_" + key))); //!enabledAfterStep_transName[s, s', t, genEvents]\n
            else
                expr = ExprBinary.Op.OR.make(null, null, expr, ExprUnary.Op.NOT.make(null, ExprBadJoin.make(null, null, sSPrimeGenEvnt, ExprVar.make(null, "enabledAfterStep_" + key))));
        }
    }

    /*
     * This function creates an AST for the following predicate: pred isEnabled[s:
     * Snapshot] {}
     */
    static void createIsEnabledAST(DashModule module) {
        Expr expr = null;
        for (String key : module.transitions.keySet()) {
            if (expr == null)
                expr = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "pre_" + key)); //pre_transName[s]
            else
                expr = ExprBinary.Op.OR.make(null, null, expr, ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "pre_" + key)));
        }
    }

    /*
     * This function creates an AST for the following predicate: pred equals[s, s':
     * Snapshot] {}
     */
    static void createEqualsAST(DashModule module) {
        ExprVar s = ExprVar.make(null, "s");
        ExprVar sPrime = ExprVar.make(null, "s'");
        ExprVar conf = ExprVar.make(null, "conf");
        ExprVar events = ExprVar.make(null, "events");
        ExprVar taken = ExprVar.make(null, "taken");

        Expr expr = ExprBinary.Op.EQUALS.make(null, null, ExprBadJoin.make(null, null, sPrime, conf), ExprBadJoin.make(null, null, s, conf)); //s'.conf = s.conf
        expr = ExprBinary.Op.AND.make(null, null, expr, ExprBinary.Op.EQUALS.make(null, null, ExprBadJoin.make(null, null, sPrime, events), ExprBadJoin.make(null, null, s, events))); //s'.events = s.events
        expr = ExprBinary.Op.AND.make(null, null, expr, ExprBinary.Op.EQUALS.make(null, null, ExprBadJoin.make(null, null, sPrime, taken), ExprBadJoin.make(null, null, s, taken))); //s'.taken = s.taken

        for (String key : module.variableNames.keySet()) {
            for (String var : module.variableNames.get(key))
                expr = ExprBinary.Op.AND.make(null, null, expr, ExprBinary.Op.EQUALS.make(null, null, ExprBadJoin.make(null, null, sPrime, ExprVar.make(null, key + "_" + var)), ExprBadJoin.make(null, null, s, ExprVar.make(null, key + "_" + var))));
        }
    }

    /* This function creates the AST for the init conditions */
    static void createInitAST(DashModule module) {
        ExprVar s = ExprVar.make(null, "s");
        ExprVar conf = ExprVar.make(null, "conf");
        ExprVar events = ExprVar.make(null, "events");
        ExprVar taken = ExprVar.make(null, "taken");

        Expr binaryLeft = ExprBadJoin.make(null, null, s, conf);
        Expr binaryRight = null;

        for (DashState state : module.defaultStates) {
            if (binaryRight == null)
                binaryRight = ExprVar.make(null, state.modifiedName);
            else
                binaryRight = ExprBinary.Op.PLUS.make(null, null, binaryRight, ExprVar.make(null, state.modifiedName));
        }
        for (DashConcState concState : module.concStates.values()) {
            if (concState.states.size() == 0) {
                if (binaryRight == null)
                    binaryRight = ExprVar.make(null, concState.modifiedName);
                else
                    binaryRight = ExprBinary.Op.PLUS.make(null, null, binaryRight, ExprVar.make(null, concState.modifiedName));
            }
        }

        Expr expression = ExprBinary.Op.EQUALS.make(null, null, binaryLeft, binaryRight);

        expression = ExprBinary.Op.AND.make(null, null, expression, ExprUnary.Op.NO.make(null, ExprBadJoin.make(null, null, s, taken))); //no s.taken
        Expr binary = ExprBinary.Op.INTERSECT.make(null, null, ExprBadJoin.make(null, null, s, events), ExprVar.make(null, "InternalEvent")); //no s.events & InternalEvent
        expression = ExprBinary.Op.AND.make(null, null, expression, binary);

        for (DashInit init : module.initConditions) {
            for (Expr expr : init.exprList) {
                getVarFromParentExpr(expr, init.parent, module);
                expression = ExprBinary.Op.AND.make(null, null, expression, binary);
            }
        }

    }


    //Take an expression in a do statement and modify any variables present. Eg: active_players should become
    //s.Game_active_players (Given that active_players is declared under the Game concurrent state)
    static Expr modifyExprWithVar(Expr expr, DashConcState parent, DashModule module) {
        final List<String> variablesInParent = module.variableNames.get(parent.modifiedName);
        final List<String> envVariablesInParent = module.envVariableNames.get(parent.modifiedName);

        Expr expression = expr;

        DashConcState outerConcState = parent.parent;

        if (variablesInParent != null)
            expression = modifyVar(expression, parent, expr, variablesInParent);
        if (envVariablesInParent != null)
            expression = modifyVar(expression, parent, expr, envVariablesInParent);

        while (outerConcState != null) {
            if (module.variableNames.get(outerConcState.modifiedName) != null)
                expression = modifyVar(expression, outerConcState, expr, module.variableNames.get(outerConcState.modifiedName));
            if (module.envVariableNames.get(parent.modifiedName) != null)
                expression = modifyVar(expression, outerConcState, expr, module.envVariableNames.get(parent.modifiedName));
            outerConcState = outerConcState.parent;
        }

        return expression;
    }

    static Expr modifyVar(Expr expression, DashConcState parent, Expr expr, List<String> exprList) {
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
            parentExpr = modifyExprWithVar((ExprVar) parentExpr, parent, module);
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
            (binary.left) = modifyExprWithVar(binary.left, parent, module);
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
            (binary.right) = modifyExprWithVar(binary.right, parent, module);
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
            unary.sub = modifyExprWithVar(unary.sub, parent, module);
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
            joinExpr.left = modifyExprWithVar(joinExpr.left, parent, module);
        }
        if (joinExpr.left instanceof ExprUnary) {
            getVarFromUnary((ExprUnary) joinExpr.left, parent, module);
        }
        if (joinExpr.left instanceof ExprBadJoin) {
            getVarFromBadJoin((ExprBadJoin) joinExpr.right, parent, module);
        }
        if (joinExpr.right instanceof ExprVar) {
            joinExpr.right = modifyExprWithVar(joinExpr.right, parent, module);
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
            exprQt.sub = modifyExprWithVar(exprQt.sub, parent, module);
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

    //Find the variables that are unchanged during a transition
    static List<String> getUnchangedVars(List<Expr> exprList, DashConcState parent, DashModule module) {
        List<String> variablesInParent = new ArrayList<String>();
        List<String> unchangedVars = new ArrayList<String>();

        if (module.variableNames.get(parent.modifiedName) != null) {
            variablesInParent = new ArrayList<String>(module.variableNames.get(parent.modifiedName));
            unchangedVars = new ArrayList<String>(module.variableNames.get(parent.modifiedName));
        }

        for (Expr expr : exprList) {
            //If we find an expression that is binary,
            //we check the left side of the binary expression and remove the var from our list of
            //vars that are unchanged
            if (expr instanceof ExprBinary) {
                for (String var : variablesInParent)
                    if (((ExprBinary) expr).left.toString().contains(var))
                        unchangedVars.remove(var);
            }
        }
        return unchangedVars;
    }

    /* ONLY FOR TESTING */
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


/*
 * //System.out.println("Expr: " + expr.toString() + " type: " +
 * expr.getClass()); //System.out.println("Expr Right: " + ((ExprBinary)
 * expr).right + " type: " + ((ExprBinary) expr).right.getClass()); //ExprBinary
 * binRight = (ExprBinary) ((ExprBinary) expr).right;
 * //System.out.println("Expr Right Right: " + binRight.right + " type: " +
 * ((ExprBinary) expr).right.getClass());
 * //System.out.println("Expr Right Left: " + binRight.left + " type: " +
 * ((ExprBinary) expr).right.getClass()); ExprVar leftConf = ExprVar.make(null,
 * "s.Elevator_conf"); ExprVar rightConf = ExprVar.make(null,
 * "s.Elevator_conf"); ExprVar direction = ExprVar.make(null,
 * "s.Elevator_direction"); ExprVar called = ExprVar.make(null,
 * "s.Elevator_called"); Expr ExprBinConfDir = ExprBinary.Op.PLUS.make(null,
 * null, rightConf, direction); Expr ExprRight = ExprBinary.Op.MINUS.make(null,
 * null, ExprBinConfDir, called); Expr expr = ExprBinary.Op.EQUALS.make(null,
 * null, leftConf, ExprRight); System.out.println("User Gen Expr: " +
 * expr.toString()); System.out.println("User Expr: " + expr.toString() +
 * " type: " + expr.getClass()); System.out.println("User Expr Right: " +
 * ((ExprBinary) expr).right + " type: " + ((ExprBinary)
 * expr).right.getClass()); ExprBinary binRight = (ExprBinary) ((ExprBinary)
 * expr).right; System.out.println("User Expr Right Right: " + binRight.right +
 * " type: " + ((ExprBinary) expr).right.getClass());
 * System.out.println("User Expr Right Left: " + binRight.left + " type: " +
 * ((ExprBinary) expr).right.getClass()); System.out.println("\n\n\n\n\n");
 */
