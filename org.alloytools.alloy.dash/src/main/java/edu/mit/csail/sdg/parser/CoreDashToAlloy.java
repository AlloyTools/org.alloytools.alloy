package edu.mit.csail.sdg.parser;

import java.util.ArrayList;
import java.util.Arrays;
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

public class CoreDashToAlloy {

    public static void convertToAlloyAST(DashModule module) {
        module.status = 0;
        //module.addModelName(null, "Elevator", new ArrayList<ExprVar>());
        module.addOpen(null, null, ExprVar.make(null, "util/Boolean"), new ArrayList<ExprVar>(), null);
        module.addOpen(null, null, ExprVar.make(null, "util/steps"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "Snapshot"))), null);
        module.addOpen(null, null, ExprVar.make(null, "util/ordering"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "Snapshot"))), null);
        createSnapshotSigAST(module);
        createStateSpaceAST(module);
        createEventSpaceAST(module);
        createTransitionSpaceAST(module);
        createTransitionsAST(module);

        createInitAST(module);
        createOperationAST(module);
        createSmallStepAST(module);
        createTestIfStableAST(module);
        createIsEnabledAST(module);
        createEqualsAST(module);
        createPathAST(module);
        createModelDefFact(module);
    }

    /* Used by other functions to help create signature ASTs */
    static void addSigAST(DashModule module, String sigName, ExprVar isExtends, List<ExprVar> sigParent, List<Decl> decls, Pos isAbstract, Pos isLone, Pos isOne, Pos isSome, Pos isPrivate) {
        module.addSig(sigName, isExtends, sigParent, decls, null, null, AttrType.ABSTRACT.makenull(isAbstract), AttrType.LONE.makenull(isLone), AttrType.ONE.makenull(isOne), AttrType.SOME.makenull(isSome), AttrType.PRIVATE.makenull(isPrivate));
    }

    static void createTransitionsAST(DashModule module) {
        for (DashTrans transition : module.transitions.values()) {
            createPreConditionAST(transition, module);
            createPostConditionAST(transition, module);
            createSemanticsAST(transition, module);
            createTransCallAST(transition, module);
            createEnabledNextStepAST(transition, module);
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

        if (DashOptions.isEnvEventModel) {
            Expr b = ExprUnary.Op.SETOF.make(null, ExprVar.make(null, "EventLabel"));
            a.add(ExprVar.make(null, "events"));
            decls.add(new Decl(null, null, null, null, a, mult(b)));//events: set Label
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

    static void createStateSpaceAST(DashModule module) {
        addSigAST(module, "SystemState", ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "StateLabel"))), new ArrayList<Decl>(), new Pos("abstract", 0, 0), null, null, null, null);

        for (DashConcState concState : module.topLevelConcStates.values()) {
            addSigAST(module, concState.modifiedName, ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "SystemState"))), new ArrayList<Decl>(), new Pos("abstract", 0, 0), null, null, null, null);
            createStateAST(concState, module);
        }
    }

    static void createStateAST(DashConcState concState, DashModule module) {
        for (DashState state : concState.states) {
            addSigAST(module, state.modifiedName, ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, concState.modifiedName))), new ArrayList<Decl>(), null, null, new Pos("one", 0, 0), null, null);
        }

        for (DashConcState innerConcState : concState.concStates) {
            addSigAST(module, innerConcState.modifiedName, ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, concState.modifiedName))), new ArrayList<Decl>(), new Pos("abstract", 0, 0), null, null, null, null);
            createStateAST(innerConcState, module);
        }
    }

    static void createEventSpaceAST(DashModule module) {
        for (String key : module.events.keySet()) {
            if (!module.events.get(key).type.equals("env"))
                addSigAST(module, key, ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "EnvironmentEvent"))), new ArrayList<Decl>(), null, null, new Pos("one", 0, 0), null, null);
        }
    }

    static void createTransitionSpaceAST(DashModule module) {
        for (DashTrans transition : module.transitions.values()) {
            System.out.println("Trans Name: " + transition.modifiedName);
            addSigAST(module, transition.modifiedName, ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "TransitionLabel"))), new ArrayList<Decl>(), null, null, new Pos("one", 0, 0), null, null);
        }
    }

    /*
     * Create the pre-conditions AST and returns it. Is used both for creating the
     * pre-cond predicate and for adding pre-conditions to the
     * enabledAfterStep_transName predicate
     */
    static Expr getPreCondAST(DashTrans transition, DashModule module) {
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
        if (transition.onExpr.name != null && DashOptions.isEnvEventModel) {
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

        return expression;
    }

    /*
     * This function creates the AST for the precondition predicate in the Alloy
     * Model
     */
    static void createPreConditionAST(DashTrans transition, DashModule module) {
        Expr expression = null;
        expression = ExprUnary.Op.NOOP.make(null, getPreCondAST(transition, module));
        System.out.println("PreCond: " + expression.toString() + '\n');
        addPredicateAST(module, "pre_" + transition.modifiedName, "s", null, null, null, expression);
    }

    /*
     * This function creates the AST for the postcondition predicate in the Alloy
     * Model
     */
    static void createPostConditionAST(DashTrans transition, DashModule module) {
        Expr sStable = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "stable"));
        Expr sPrimeStable = ExprBadJoin.make(null, null, ExprVar.make(null, "s'"), ExprVar.make(null, "stable"));
        Expr sEvents = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "events"));
        Expr sPrimeEvents = ExprBadJoin.make(null, null, ExprVar.make(null, "s'"), ExprVar.make(null, "events"));
        ExprVar intEvent = ExprVar.make(null, "InternalEvent");
        ExprVar extEvent = ExprVar.make(null, "ExternalEvent");
        Expr expression = null;

        Expr binaryGoTo = null;
        /*
         * Creating the following expression: s'.conf = s.conf - sourceState +
         * destinationState
         */
        if (transition.gotoExpr.gotoExpr.size() > 0) {
            Expr gotoExpr = ExprVar.make(null, transition.gotoExpr.gotoExpr.get(0).replace('/', '_'));
            Expr fromExpr = ExprVar.make(null, transition.fromExpr.fromExpr.get(0).replace('/', '_'));
            Expr sConf = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "conf")); //s.conf
            Expr sConfPrime = ExprBadJoin.make(null, null, ExprVar.make(null, "s'"), ExprVar.make(null, "conf"));//s'.conf
            Expr binaryRight = ExprBinary.Op.PLUS.make(null, null, ExprBinary.Op.MINUS.make(null, null, sConf, fromExpr), gotoExpr);//s.conf - fromExpr + gotoExpr
            expression = ExprBinary.Op.EQUALS.make(null, null, sConfPrime, binaryRight); //s'.conf = s.conf - fromExpr + gotoExpr
        }

        /* Creating the following expression: no (s'.events & InternalEvent) */
        Expr sendExpr = null;
        if (transition.sendExpr.name == null && DashOptions.isEnvEventModel) {
            Expr join = ExprBadJoin.make(null, null, ExprVar.make(null, "s'"), ExprVar.make(null, "events")); // s'.events
            Expr rightBinary = ExprBinary.Op.INTERSECT.make(null, null, join, ExprVar.make(null, "InternalEvent")); // s'.events & InternalEvent
            sendExpr = ExprUnary.Op.NO.make(null, rightBinary); // no (s'.events & InternalEvent)
        }
        /* Creating the following expression: sentEvent in s'.events */
        else if (transition.sendExpr != null && transition.sendExpr.name != null) {
            Expr join = ExprBadJoin.make(null, null, ExprVar.make(null, "s'"), ExprVar.make(null, "events")); // s'.events
            sendExpr = ExprBinary.Op.IN.make(null, null, ExprVar.make(null, transition.sendExpr.name), mult(join)); // sentEvent in s'.events
        }

        if (sendExpr != null)
            expression = ExprBinary.Op.AND.make(null, null, expression, sendExpr);

        /* Creating the following expression: AND[doexpr, doexpr, ..] */
        if (transition.doExpr != null && transition.doExpr.exprList != null) {
            for (Expr expr : transition.doExpr.exprList) {
                getVarFromParentExpr(expr, getParentConcState(transition.parentState), module);
                expression = ExprBinary.Op.AND.make(null, null, expression, expr);
            }
            //These are the variables that have not been changed in the post-cond and they need to retain their values in the next snapshot
            for (String var : getUnchangedVars(transition.doExpr.exprList, getParentConcState(transition.parentState), module)) {
                Expr binaryLeft = ExprBadJoin.make(null, null, ExprVar.make(null, "s'"), ExprVar.make(null, var)); //s'.variableParent_varName
                Expr binaryRight = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, var)); //s'.variableParent_varName
                Expr binaryEquals = ExprBinary.Op.EQUALS.make(null, null, binaryLeft, binaryRight);
                expression = ExprBinary.Op.AND.make(null, null, expression, binaryEquals);
            }
        }

        /* Creating the following expression(s): s'.variable = s.variable */
        if (transition.doExpr == null) {
            //These are the variables that have not been changed in the post-cond and they need to retain their values in the next snapshot
            for (String var : getUnchangedVars(new ArrayList<Expr>(), getParentConcState(transition.parentState), module)) {
                Expr binaryLeft = ExprBadJoin.make(null, null, ExprVar.make(null, "s'"), ExprVar.make(null, var)); //s'.variableParent_varName
                Expr binaryRight = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, var)); //s'.variableParent_varName
                Expr binaryEquals = ExprBinary.Op.EQUALS.make(null, null, binaryLeft, binaryRight);
                expression = ExprBinary.Op.AND.make(null, null, expression, binaryEquals);
            }
        }


        /*
         * Creating the following expression: testIfNextStable[s, s', {none},
         * Mutex_Process1_wait] => { s'.stable = True } else { s'.stable = False }
         */
        if (module.stateHierarchy && !DashOptions.isEnvEventModel) {
            Expr ifExpr = ExprBinary.Op.EQUALS.make(null, null, ExprBadJoin.make(null, null, ExprVar.make(null, "s'"), ExprVar.make(null, "stable")), ExprVar.make(null, "True"));
            Expr ElseExpr = ExprBinary.Op.EQUALS.make(null, null, ExprBadJoin.make(null, null, ExprVar.make(null, "s'"), ExprVar.make(null, "stable")), ExprVar.make(null, "False"));
            Expr ifCond = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "testIfNextStable"));
            ifCond = ExprBadJoin.make(null, null, ExprVar.make(null, "s'"), ifCond);
            ifCond = ExprBadJoin.make(null, null, ExprVar.make(null, transition.modifiedName), ifCond);
            ifCond = ExprBadJoin.make(null, null, ExprVar.make(null, "none"), ifCond);
            Expr ifElseExpr = ExprITE.make(null, ifCond, ifExpr, ElseExpr);
            expression = ExprBinary.Op.AND.make(null, null, expression, ifElseExpr);
        }

        /*
         * Creating the following expression: testIfNextStable[s, s', {none},
         * Elevator_Controller_sendReq] => { s'.stable = True s.stable = True => { no
         * ((s'.events & InternalEvent) ) } else { no ((s'.events & InternalEvent) - {
         * (InternalEvent & s.events)}) } } else { s'.stable = False s.stable = True =>
         * { s'.events & InternalEvent = {none} s'.events & EnvironmentEvent = s.events
         * & EnvironmentEvent } else { s'.events = s.events + {none} } }
         */
        if (module.stateHierarchy && DashOptions.isEnvEventModel) {
            Expr sPrimeStableTrue = ExprBinary.Op.EQUALS.make(null, null, sPrimeStable, ExprVar.make(null, "True")); //s'.stable = True
            Expr sPrimeStableFalse = ExprBinary.Op.EQUALS.make(null, null, sPrimeStable, ExprVar.make(null, "False")); //s'.stable = True
            Expr sStableTrue = ExprBinary.Op.EQUALS.make(null, null, sStable, ExprVar.make(null, "True")); //s.stable = True
            Expr sPrimeEnvAndIntEvn = ExprBinary.Op.INTERSECT.make(null, null, sPrimeEvents, intEvent); //s'events & InternalEvent
            Expr sEnvAndIntEvn = ExprBinary.Op.INTERSECT.make(null, null, intEvent, sEvents); //s.events & InternalEvent
            Expr noSPrimeEnvAndIntEvn = ExprUnary.Op.NO.make(null, sPrimeEnvAndIntEvn); //no (s'events & InternalEvent)
            Expr noSPrimeEnvAndIntEvnMinus = ExprUnary.Op.NO.make(null, ExprBinary.Op.MINUS.make(null, null, sPrimeEnvAndIntEvn, sEnvAndIntEvn)); // no ((s'events & InternalEvent) - (s.events & InternalEvent))
            Expr ifLowerExpr = ExprITE.make(null, sStableTrue, noSPrimeEnvAndIntEvn, noSPrimeEnvAndIntEvnMinus);

            ifLowerExpr = ExprBinary.Op.AND.make(null, null, ifLowerExpr, sPrimeStableTrue);

            Expr elseLowerExprIf = ExprBinary.Op.EQUALS.make(null, null, sPrimeEnvAndIntEvn, ExprVar.make(null, "none")); //s'.events & InternalEvent = {none}
            Expr sPrimeEvtAndEnv = ExprBinary.Op.INTERSECT.make(null, null, sPrimeEvents, ExprVar.make(null, "EnvironmentEvent")); //s'.events & EnvironmentEvent
            Expr sEventAndEnv = ExprBinary.Op.INTERSECT.make(null, null, sEvents, ExprVar.make(null, "EnvironmentEvent")); //s.events & EnvironmentEvent
            elseLowerExprIf = ExprBinary.Op.AND.make(null, null, elseLowerExprIf, ExprBinary.Op.EQUALS.make(null, null, sPrimeEvtAndEnv, sEventAndEnv));

            Expr elseLowerElse = ExprBinary.Op.EQUALS.make(null, null, sPrimeEvents, ExprBinary.Op.PLUS.make(null, null, sEvents, ExprVar.make(null, "none")));

            Expr elseLowerExpr = ExprITE.make(null, sStableTrue, elseLowerExprIf, elseLowerElse);
            elseLowerExpr = ExprBinary.Op.AND.make(null, null, elseLowerExpr, sPrimeStableFalse);

            Expr tFuncCall = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "testIfNextStable")); //s.testIfNextStable
            Expr genEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "s'"), tFuncCall); //s'.s.enabledAfterStep_transName
            Expr sPrimeGenEventT = ExprBadJoin.make(null, null, ExprVar.make(null, transition.modifiedName), genEventT); //tranName.s'.s.enabledAfterStep_transName
            Expr ssPrimeGenEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "none"), sPrimeGenEventT); // none.tranName.s'.s.enabledAfterStep_transName

            expression = ExprBinary.Op.AND.make(null, null, expression, ExprITE.make(null, ssPrimeGenEventT, ifLowerExpr, elseLowerExprIf));
        }

        System.out.println("Post Cond Expression: " + expression.toString() + '\n');
        expression = ExprUnary.Op.NOOP.make(null, expression);

        System.out.println("Post Cond Expression: " + expression.toString() + '\n');
        addPredicateAST(module, "post_" + transition.modifiedName, "s", "s'", null, null, expression); //LOOK HERE
    }

    /*
     * This function creates the AST for the Semantics predicate in the Alloy Model
     */
    static void createSemanticsAST(DashTrans transition, DashModule module) {
        Expr expression = null;

        /* Creating the following expression: s'.taken = currentTrans */
        Expr semanticsExpr = null;
        Expr sTakenPrime = ExprBadJoin.make(null, null, ExprVar.make(null, "s'"), ExprVar.make(null, "taken")); //s'.taken
        Expr sTaken = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "taken")); //s.taken
        if (!module.stateHierarchy) {
            semanticsExpr = ExprBinary.Op.EQUALS.make(null, null, sTakenPrime, ExprVar.make(null, transition.modifiedName)); //s'.taken = currentTrans
            expression = semanticsExpr;
        }

        /*
         * Creating the following expression: s.stable = True => (s'.taken + transName)
         * else { )
         */
        Expr ifElseExpr = null;
        if (module.stateHierarchy) {
            Expr ifCond = ExprBinary.Op.EQUALS.make(null, null, ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "stable")), ExprVar.make(null, "True")); //s.stable = True
            Expr ifExpr = ExprBinary.Op.EQUALS.make(null, null, sTakenPrime, ExprVar.make(null, transition.modifiedName)); //s'.taken = currentTrans
            Expr ElseExprLeft = ExprBinary.Op.EQUALS.make(null, null, sTakenPrime, ExprBinary.Op.PLUS.make(null, null, sTaken, ExprVar.make(null, transition.modifiedName))); // s'.taken = s.taken + transName
            Expr ElseExprRight = null;
            Expr ElseRightBinPlus = null;
            for (DashTrans trans : module.transitions.values()) {
                if (getParentConcState(trans.parentState).modifiedName.equals(getParentConcState(transition.parentState).modifiedName)) {
                    if (ElseRightBinPlus == null)
                        ElseRightBinPlus = ExprVar.make(null, trans.modifiedName);
                    else
                        ElseRightBinPlus = ExprBinary.Op.PLUS.make(null, null, ElseRightBinPlus, ExprVar.make(null, trans.modifiedName));
                }
            }
            ElseExprRight = ExprBinary.Op.INTERSECT.make(null, null, sTaken, ElseRightBinPlus); //no (s.taken & transNames)
            ElseExprRight = ExprUnary.Op.NO.make(null, ElseExprRight);
            Expr ElseExpr = ExprBinary.Op.AND.make(null, null, ElseExprLeft, ElseExprRight);
            ifElseExpr = ExprITE.make(null, ifCond, ifExpr, ElseExpr);
            expression = ifElseExpr;
        }

        System.out.println("Semantics AST: " + expression.toString() + '\n');
        expression = ExprUnary.Op.NOOP.make(null, expression);
        addPredicateAST(module, "semantics_" + transition.modifiedName, "s", "s'", null, null, expression);
    }

    /*
     * This function creates the AST for the transition call (the one that refers to
     * the pre,post,semantics) predicate in the Alloy Model
     */
    static void createTransCallAST(DashTrans transition, DashModule module) {
        ExprVar s = ExprVar.make(null, "s");
        ExprVar sPrime = ExprVar.make(null, "s'");

        Expr expression = null;

        /*
         * Creating the following expressions: post_transName[s, s'],
         * semantics_transName[s, s'], pre_transName[s]
         */
        Expr postTransCall = ExprBadJoin.make(null, null, s, ExprVar.make(null, "post_" + transition.modifiedName)); //s.post_transName
        postTransCall = ExprBadJoin.make(null, null, sPrime, postTransCall); //s'.s.post_transName

        Expr sematicsCall = ExprBadJoin.make(null, null, s, ExprVar.make(null, "semantics_" + transition.modifiedName)); //s.sematics_transName
        sematicsCall = ExprBadJoin.make(null, null, sPrime, sematicsCall); //s'.s.sematics_transName

        expression = ExprBinary.Op.AND.make(null, null, postTransCall, sematicsCall); //AND[postTransCall, semanticsCall]

        Expr preTransCall = ExprBadJoin.make(null, null, s, ExprVar.make(null, "pre_" + transition.modifiedName)); //s.pre_transName

        expression = ExprBinary.Op.AND.make(null, null, expression, preTransCall); //AND[postTransCall, semanticsCall, preTransCall]
        addPredicateAST(module, transition.modifiedName, "s", "s'", null, null, expression);
    }

    /*
     * This function creates an AST for the following predicate: pred
     * enabledAfterStep_transName[_s, s: Snapshot] {expressions}
     */
    static void createEnabledNextStepAST(DashTrans transition, DashModule module) {
        Expr expr = null;
        if (module.stateHierarchy) {
            expr = getPreCondAST(transition, module); //Store all the pre-conditions

            Expr ifCond = ExprBinary.Op.EQUALS.make(null, null, ExprBadJoin.make(null, null, ExprVar.make(null, "_s"), ExprVar.make(null, "stable")), ExprVar.make(null, "True")); //s.stable = True
            Expr ifExprLeft = ExprVar.make(null, "t");
            Expr ifExprRight = null;
            for (DashTrans trans : module.transitions.values()) {
                if (getParentConcState(trans.parentState).modifiedName.equals(getParentConcState(transition.parentState).modifiedName)) {
                    if (ifExprRight == null)
                        ifExprRight = ExprVar.make(null, trans.modifiedName);
                    else
                        ifExprRight = ExprBinary.Op.PLUS.make(null, null, ifExprRight, ExprVar.make(null, trans.modifiedName));
                }
            }
            Expr ifExpr = ExprBinary.Op.INTERSECT.make(null, null, ifExprLeft, ifExprRight);
            ifExpr = ExprUnary.Op.NO.make(null, ifExpr);

            if (DashOptions.isEnvEventModel && transition.onExpr != null && transition.onExpr.name != null) {
                Expr _sEvent = ExprBadJoin.make(null, null, ExprVar.make(null, "_s"), ExprVar.make(null, "events"));
                Expr binaryIntersect = ExprBinary.Op.INTERSECT.make(null, null, _sEvent, ExprVar.make(null, "EnvironmentEvent"));
                Expr binaryPlus = ExprBinary.Op.PLUS.make(null, null, binaryIntersect, ExprVar.make(null, "genEvents"));
                Expr binaryIn = ExprBinary.Op.IN.make(null, null, ExprVar.make(null, transition.onExpr.name), binaryPlus);
                ifExpr = ExprBinary.Op.AND.make(null, null, ifExpr, binaryIn);
            }


            Expr elseExpr = null;
            Expr elseExprLeft = ExprBinary.Op.PLUS.make(null, null, ExprBadJoin.make(null, null, ExprVar.make(null, "_s"), ExprVar.make(null, "taken")), ExprVar.make(null, "t")); //_s.taken + t
            Expr elseExprRight = null;
            for (DashTrans trans : module.transitions.values()) {
                if (getParentConcState(trans.parentState).modifiedName.equals(getParentConcState(transition.parentState).modifiedName)) {
                    if (elseExprRight == null)
                        elseExprRight = ExprVar.make(null, trans.modifiedName);
                    else
                        elseExprRight = ExprBinary.Op.PLUS.make(null, null, elseExprRight, ExprVar.make(null, trans.modifiedName));
                }
            }
            elseExpr = ExprBinary.Op.INTERSECT.make(null, null, elseExprLeft, elseExprRight);
            elseExpr = ExprUnary.Op.NO.make(null, elseExpr);

            if (DashOptions.isEnvEventModel && transition.onExpr != null && transition.onExpr.name != null) {
                Expr _sEvent = ExprBadJoin.make(null, null, ExprVar.make(null, "_s"), ExprVar.make(null, "events"));
                Expr binaryPlus = ExprBinary.Op.PLUS.make(null, null, _sEvent, ExprVar.make(null, "genEvents"));
                Expr binaryIn = ExprBinary.Op.IN.make(null, null, ExprVar.make(null, transition.onExpr.name), binaryPlus);
                elseExpr = ExprBinary.Op.AND.make(null, null, ifExpr, binaryIn);
            }

            expr = ExprBinary.Op.AND.make(null, null, expr, ExprITE.make(null, ifCond, ifExpr, elseExpr));

            System.out.println("Expr from EnabledNextStep: " + expr.toString() + '\n');
            addPredicateAST(module, "enabledAfterStep_" + transition.modifiedName, "_s", "s", "t", "genEvents", expr);
        }
    }

    /*
     * This function creates an AST for the following predicate: pred small_step[s,
     * s': Snapshot] { operation[s, s'] }
     */
    static void createSmallStepAST(DashModule module) {
        Expr operationCall = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "operation"));
        operationCall = ExprBadJoin.make(null, null, ExprVar.make(null, "s'"), operationCall);

        addPredicateAST(module, "small_step", "s", "s'", null, null, operationCall);
    }

    static void createPathAST(DashModule module) {
        List<Decl> decls = new ArrayList<Decl>();
        ExprVar s = ExprVar.make(null, "s");
        ExprVar sPrime = ExprVar.make(null, "s'");
        List<ExprVar> a = new ArrayList<ExprVar>(Arrays.asList(s)); //[s]
        Expr snapshot = ExprUnary.Op.ONE.make(null, ExprVar.make(null, "Snapshot"));
        Expr sNext = ExprBadJoin.make(null, null, s, ExprVar.make(null, "next")); //s.next

        Expr expression = null;

        decls.add(new Decl(null, null, null, null, a, mult(snapshot))); //s: Snapshot

        a = new ArrayList<ExprVar>(Arrays.asList(sPrime));

        decls.add(new Decl(null, null, null, null, a, mult(sNext))); //s': s.next

        Expr operationCall = ExprBadJoin.make(null, null, s, ExprVar.make(null, "operation"));
        operationCall = ExprBadJoin.make(null, null, sPrime, operationCall); //s'.s.operation

        expression = ExprQt.Op.ALL.make(null, null, decls, operationCall);

        expression = ExprBinary.Op.AND.make(null, null, expression, ExprBadJoin.make(null, null, ExprVar.make(null, "first"), ExprVar.make(null, "init")));

        System.out.println("Path AST: " + expression.toString() + '\n');
        addPredicateAST(module, "path", null, null, null, null, expression);
    }


    /*
     * This function creates an AST for the facts in the Model Definition
     */
    static void createModelDefFact(DashModule module) {
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        Expr snapshot = ExprUnary.Op.ONE.make(null, ExprVar.make(null, "Snapshot"));
        Expr s = ExprVar.make(null, "s");
        Expr sPrime = ExprVar.make(null, "s'");
        Expr ssPrime = ExprBadJoin.make(null, null, s, sPrime);

        Expr expression = null; //This is the final expression to be stored in the Fact AST

        /*
         * Creating the following expression: all s: Snapshot | s in initial iff init[s]
         */
        a.add((ExprVar) s);
        decls.add(new Decl(null, null, null, null, a, mult(snapshot))); //s: Snapshot
        Expr rightQT = ExprBinary.Op.IFF.make(null, null, ExprBinary.Op.IN.make(null, null, s, ExprVar.make(null, "initial")), ExprBadJoin.make(null, null, s, ExprVar.make(null, "init")));
        expression = ExprQt.Op.ALL.make(null, null, new ArrayList<Decl>(decls), rightQT); //all s: Snapshot | s in initial iff init[s]
        a.clear();
        decls.clear();

        /*
         * Creating the following expression: all s, s': Snapshot | s->s' in nextStep
         * iff small_step[s, s']
         */
        a.add((ExprVar) s);
        a.add((ExprVar) sPrime);
        decls.add(new Decl(null, null, null, null, a, mult(snapshot))); //s: Snapshot
        Expr sArrowSPrime = ExprBinary.Op.ARROW.make(null, null, s, sPrime);
        Expr smallStepCall = ExprBadJoin.make(null, null, s, ExprVar.make(null, "small_step"));//s'.small_step
        smallStepCall = ExprBadJoin.make(null, null, sPrime, smallStepCall); //s.s'.small_step
        rightQT = ExprBinary.Op.IFF.make(null, null, ExprBinary.Op.IN.make(null, null, sArrowSPrime, ExprVar.make(null, "nextStep")), smallStepCall);
        Expr expr = ExprQt.Op.ALL.make(null, null, new ArrayList<Decl>(decls), rightQT); //all s, s': Snapshot | s->s' in nextStep iff small_step[s, s']

        expression = ExprBinary.Op.AND.make(null, null, expression, expr);

        /*
         * Creating the following expression: all s, s': Snapshot | equals[s, s'] => s =
         * s'
         */
        Expr equalsCall = ExprBadJoin.make(null, null, s, ExprVar.make(null, "equals"));//s.small_step
        equalsCall = ExprBadJoin.make(null, null, sPrime, equalsCall); //s'.s.small_step
        rightQT = ExprBinary.Op.IFF.make(null, null, equalsCall, ExprBinary.Op.EQUALS.make(null, null, s, sPrime));
        expr = ExprQt.Op.ALL.make(null, null, new ArrayList<Decl>(decls), rightQT); //all s, s': Snapshot | equals[s, s'] => s = s'
        a.clear();
        decls.clear();

        expression = ExprBinary.Op.AND.make(null, null, expression, expr);

        /*
         * Creating the following expression: all s': Snapshot | (isEnabled[s] && no s':
         * Snapshot | small_step[s, s']) => s.stable = False
         */
        Expr isEnabledCall = ExprBadJoin.make(null, null, s, ExprVar.make(null, "isEnabled"));
        a.add((ExprVar) sPrime);
        decls.add(new Decl(null, null, null, null, a, mult(snapshot))); //s': Snapshot
        Expr qtExpr = ExprQt.Op.NO.make(null, null, decls, smallStepCall);// no s': Snapshot | small_step[s, s']
        Expr iffLeft = ExprBinary.Op.AND.make(null, null, isEnabledCall, qtExpr); //(isEnabled[s] && no s': Snapshot | small_step[s, s'])
        Expr iffRight = ExprBinary.Op.EQUALS.make(null, null, ExprBadJoin.make(null, null, s, ExprVar.make(null, "stable")), ExprVar.make(null, "False")); //s.stable = False
        Expr iffExpr = ExprBinary.Op.IFF.make(null, null, iffLeft, iffRight); //(isEnabled[s] && no s': Snapshot | small_step[s, s']) => s.stable = False
        a.clear();
        decls.clear();
        a.add((ExprVar) s);
        decls.add(new Decl(null, null, null, null, a, mult(snapshot))); //s: Snapshot
        expr = ExprQt.Op.ALL.make(null, null, decls, iffExpr);//all s': Snapshot | (isEnabled[s] && no s': Snapshot | small_step[s, s']) => s.stable = False

        if (module.stateHierarchy)
            expression = ExprBinary.Op.AND.make(null, null, expression, expr);
        /*
         * Creating the following expression: all s: Snapshot | s.stable = False => some
         * s.nextStep
         */
        iffLeft = ExprBinary.Op.EQUALS.make(null, null, ExprBadJoin.make(null, null, s, ExprVar.make(null, "stable")), ExprVar.make(null, "False")); //s.stable = False
        iffRight = ExprUnary.Op.SOME.make(null, ExprBadJoin.make(null, null, s, ExprVar.make(null, "nextStep")));
        iffExpr = ExprBinary.Op.IFF.make(null, null, iffLeft, iffRight);
        expr = ExprQt.Op.ALL.make(null, null, decls, iffExpr);

        if (module.stateHierarchy)
            expression = ExprBinary.Op.AND.make(null, null, expression, expr);

        expression = ExprBinary.Op.AND.make(null, null, expression, ExprVar.make(null, "path"));

        expression = ExprUnary.Op.NOOP.make(null, expression);
        System.out.println("Fact: " + expression.toString() + '\n');
        module.addFact(null, "", expression);
    }

    /*
     * This function creates an AST for the following predicate: pred operation[s,
     * s': Snapshot] { expressions }
     */
    static void createOperationAST(DashModule module) {
        Expr expression = null;

        for (String key : module.transitions.keySet()) {
            if (expression == null) {
                Expr expr = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, key));
                expression = ExprBadJoin.make(null, null, ExprVar.make(null, "s'"), expr);
            } else {
                Expr expr = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, key));
                expr = ExprBadJoin.make(null, null, ExprVar.make(null, "s'"), expr);
                expression = ExprBinary.Op.OR.make(null, null, expression, expr);
            }
        }

        if (expression != null) {
            addPredicateAST(module, "operation", "s", "s'", null, null, expression);
        }
    }

    /*
     * This function creates an AST for the following predicate: pred
     * testIfNextStable[s, s': Snapshot, genEvents: set InternalEvent,
     * t:TransitionLabel] {}
     */
    static void createTestIfStableAST(DashModule module) {
        Expr expr = null;

        for (String key : module.transitions.keySet()) {
            if (expr == null) {
                Expr tFuncCall = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "enabledAfterStep_" + key)); //t.enabledAfterStep_transName
                Expr genEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "s'"), tFuncCall); //genEvents.t.enabledAfterStep_transName
                Expr sPrimeGenEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "t"), genEventT);
                Expr ssPrimeGenEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "genEvents"), sPrimeGenEventT);
                System.out.println("Join: " + ssPrimeGenEventT.toString());
                expr = ExprUnary.Op.NOT.make(null, ssPrimeGenEventT); //!enabledAfterStep_transName[s, s', t, genEvents]\n
            } else {
                Expr tFuncCall = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "enabledAfterStep_" + key)); //s.enabledAfterStep_transName
                Expr genEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "s'"), tFuncCall); //s'.s.enabledAfterStep_transName
                Expr sPrimeGenEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "t"), genEventT);
                Expr ssPrimeGenEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "genEvents"), sPrimeGenEventT);
                System.out.println("Join: " + ssPrimeGenEventT.toString());
                Expr negaged = ExprUnary.Op.NOT.make(null, ssPrimeGenEventT); //!enabledAfterStep_transName[s, s', t, genEvents]\n
                expr = ExprBinary.Op.AND.make(null, null, expr, negaged);
            }
        }

        expr = ExprUnary.Op.NOOP.make(null, expr);

        System.out.println("TestIfNextStable: " + expr);
        addPredicateAST(module, "testIfNextStable", "s", "s'", "t", "genEvents", expr);
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
        System.out.println("Enabled AST: " + expr.toString() + '\n');
        addPredicateAST(module, "isEnabled", "s", null, null, null, expr);
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
        if (DashOptions.isEnvEventModel)
            expr = ExprBinary.Op.AND.make(null, null, expr, ExprBinary.Op.EQUALS.make(null, null, ExprBadJoin.make(null, null, sPrime, events), ExprBadJoin.make(null, null, s, events))); //s'.events = s.events

        expr = ExprBinary.Op.AND.make(null, null, expr, ExprBinary.Op.EQUALS.make(null, null, ExprBadJoin.make(null, null, sPrime, taken), ExprBadJoin.make(null, null, s, taken))); //s'.taken = s.taken

        for (String key : module.variableNames.keySet()) {
            for (String var : module.variableNames.get(key))
                expr = ExprBinary.Op.AND.make(null, null, expr, ExprBinary.Op.EQUALS.make(null, null, ExprBadJoin.make(null, null, sPrime, ExprVar.make(null, key + "_" + var)), ExprBadJoin.make(null, null, s, ExprVar.make(null, key + "_" + var))));
        }

        expr = ExprUnary.Op.NOOP.make(null, expr);
        addPredicateAST(module, "equals", "s", "s'", null, null, expr);
    }

    /* This function creates the AST for the init conditions */
    static void createInitAST(DashModule module) {
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        Expr b = ExprUnary.Op.ONE.make(null, ExprVar.make(null, "Snapshot"));
        a.add(ExprVar.make(null, "s"));
        decls.add(new Decl(null, null, null, null, a, mult(b))); //[s: Snapshot]

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
        if (DashOptions.isEnvEventModel) {
            Expr binary = ExprBinary.Op.INTERSECT.make(null, null, ExprBadJoin.make(null, null, s, events), ExprVar.make(null, "InternalEvent")); //s.events & InternalEvent
            Expr unary = ExprUnary.Op.NO.make(null, binary); //no s.events & InternalEvent
            expression = ExprBinary.Op.AND.make(null, null, expression, unary);
        }

        for (DashInit init : module.initConditions) {
            for (Expr expr : init.exprList) {
                getVarFromParentExpr(expr, init.parent, module);
                expression = ExprBinary.Op.AND.make(null, null, expression, expr);
            }
        }

        System.out.println("Init expression: " + expression.toString() + '\n');
        expression = ExprUnary.Op.NOOP.make(null, expression);
        module.addFunc(null, null, "init", null, decls, null, expression);
    }

    /* Add a new predicate to the Dash Module */
    static void addPredicateAST(DashModule module, String predName, String arg1, String arg2, String arg3, String arg4, Expr expression) {
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        Expr snapshot = ExprUnary.Op.ONE.make(null, ExprVar.make(null, "Snapshot"));
        if (arg1 != null)
            a.add(ExprVar.make(null, arg1));
        if (arg2 != null)
            a.add(ExprVar.make(null, arg2));
        if (arg3 != null)
            a.add(ExprVar.make(null, arg3));
        if (arg4 != null)
            a.add(ExprVar.make(null, arg4));

        if (a.size() > 0 && a.size() <= 2) //Cannot add declarations if the predicate for no arguments
            decls.add(new Decl(null, null, null, null, a, mult(snapshot)));
        else if (a.size() == 4) { //Only for EnabledAfterNextStep Predicate AST creation
            decls.add(new Decl(null, null, null, null, new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, arg1), ExprVar.make(null, arg2))), mult(snapshot)));
            decls.add(new Decl(null, null, null, null, new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, arg3))), mult(ExprUnary.Op.ONE.make(null, ExprVar.make(null, "TransitionLabel")))));
            decls.add(new Decl(null, null, null, null, new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, arg4))), mult(ExprUnary.Op.SETOF.make(null, ExprVar.make(null, "InternalEvent")))));
        }

        module.addFunc(null, null, predName, null, decls, null, expression);
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
        List<String> variables = new ArrayList<String>(module.modifiedVarNames);
        List<String> unchangedVars = new ArrayList<String>(module.modifiedVarNames);


        for (Expr expr : exprList) {
            //If we find an expression that is binary,
            //we check the left side of the binary expression and remove the var from our list of
            //vars that are unchanged
            if (expr instanceof ExprBinary) {
                for (String var : variables) {
                    if (((ExprBinary) expr).left.toString().contains(var)) {
                        unchangedVars.remove(var);
                    }
                }
            }
        }
        return unchangedVars;
    }
}
