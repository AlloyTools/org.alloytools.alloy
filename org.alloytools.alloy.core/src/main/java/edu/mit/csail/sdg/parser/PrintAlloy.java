package edu.mit.csail.sdg.parser;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import edu.mit.csail.sdg.alloy4.Options;
import edu.mit.csail.sdg.ast.DashConcState;
import edu.mit.csail.sdg.ast.DashInit;
import edu.mit.csail.sdg.ast.DashState;
import edu.mit.csail.sdg.ast.DashTrans;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprHasName;
import edu.mit.csail.sdg.ast.ExprQt;

public class PrintAlloy {

    static String alloyModel = "";

    public static void printAlloyModel(DashModule module) throws IOException {

        if (module.isUnitTest)
            return;

        printSnapshotSig(module);

        printStateSpace(module);

        printTransSpace(module);

        printTransitions(module);

        printInitalCond(module);

        printModelDefinition(module);

        BufferedWriter writer = new BufferedWriter(new FileWriter(Options.outputDir + ".als"));
        writer.write(alloyModel);

        writer.close();
    }

    static void printVariables(DashModule module) {
        if (module.stateHierarchy)
            alloyModel += ("stable: one Bool");

        for (String variableName : module.variable2Expression.keySet()) {
            alloyModel += (variableName + ": " + module.variable2Expression.get(variableName) + '\n');
        }
    }

    static void printSnapshotSig(DashModule module) {
        alloyModel += "sig Snapshot extends BaseSnapshot {\n";
        printVariables(module);
        alloyModel += "}\n\n";
    }

    static void printStateSpace(DashModule module) {
        alloyModel += "/***************************** STATE SPACE *****************************/\n";
        alloyModel += "abstract sig SystemState extends StateLabel {}\n";

        for (DashConcState concState : module.topLevelConcStates.values()) {
            alloyModel += ("abstract sig " + concState.modifiedName + " extends SystemState {}\n");
            printStateLabels(concState);
        }
        alloyModel += "}\n\n";
    }

    static void printStateLabels(DashConcState concState) {
        for (DashState state : concState.states)
            alloyModel += ("one sig " + state.modifiedName + " extends " + concState.modifiedName + "{}\n");

        for (DashConcState innerConcState : concState.concStates) {
            alloyModel += ("abstract sig " + innerConcState.modifiedName + " extends " + concState.modifiedName + "{}\n");
            printStateLabels(innerConcState);
        }
    }

    static void printTransSpace(DashModule module) {
        alloyModel += "/***************************** TRANSITION SPACE *****************************/\n";

        for (DashTrans transition : module.transitions.values()) {
            alloyModel += ("one sig " + transition.modifiedName + " extends TransitionLabel {}\n");
        }
        alloyModel += "}\n\n";
    }

    static void printTransitions(DashModule module) {
        for (DashTrans transition : module.transitions.values()) {
            printPreCondition(transition, module, false);
            printPostCondition(transition, module);
            printTransCall(transition, module);
            if (module.stateHierarchy)
                printEnabledNextStepPred(transition, module);
            printSemantics(transition, module);
        }
    }

    static void printPreCondition(DashTrans transition, DashModule module, Boolean onlyExpr) {
        //We only want to print the expressions and not the pred name
        if (!onlyExpr)
            alloyModel += ("pred pre_" + transition.modifiedName + "[s: Snapshot]" + '\n');

        if (transition.fromExpr.fromExpr.size() > 0)
            alloyModel += (transition.fromExpr.fromExpr.get(0).replace('/', '_') + " in s.conf\n");

        if (transition.onExpr.name != null)
            alloyModel += ((transition.onExpr.name).replace('/', '_') + " in (s.events & EnvironmentEvent)\n");

        if (transition.whenExpr != null) {
            for (Expr expr : transition.whenExpr.exprList)
                alloyModel += (modifyExprVariables(expr, getParentConcState(transition.parentState), module) + '\n');
        }

        if (!onlyExpr)
            alloyModel += "}\n\n";
    }

    static void printPostCondition(DashTrans transition, DashModule module) {
        alloyModel += ("pred post_" + transition.modifiedName + "[s, s': Snapshot] {" + '\n');

        if (transition.gotoExpr.gotoExpr.size() > 0)
            alloyModel += ("s'.conf = s.conf - " + transition.fromExpr.fromExpr.get(0).replace('/', '_') + " + { " + transition.gotoExpr.gotoExpr.get(0).replace('/', '_') + " }\n");

        if (transition.doExpr != null) {
            for (Expr expr : transition.doExpr.exprList)
                alloyModel += (modifyExprVariables(expr, getParentConcState(transition.parentState), module) + '\n');

            //These are the variables that have not been changed in the post-cond and they need to retain their values in the next snapshot
            for (String var : getUnchangedVars(transition.doExpr.exprList, getParentConcState(transition.parentState), module))
                alloyModel += ("s'." + getParentConcState(transition.parentState).modifiedName + "_" + var + " = s." + getParentConcState(transition.parentState).modifiedName + "_" + var + '\n');
        }

        if (transition.doExpr == null) {
            for (String var : getUnchangedVars(new ArrayList<Expr>(), getParentConcState(transition.parentState), module))
                alloyModel += ("s'." + getParentConcState(transition.parentState).modifiedName + "_" + var + " = s." + getParentConcState(transition.parentState).modifiedName + "_" + var + '\n');
        }

        if (transition.sendExpr == null)
            alloyModel += ("no (s'.events and InternalEvent) \n");

        alloyModel += "}\n\n";
    }

    static void printTransCall(DashTrans transition, DashModule module) {
        alloyModel += ("pred " + transition.modifiedName + "[s, s': Snapshot] {" + '\n');
        alloyModel += ("post_" + transition.modifiedName + "[s, s']" + '\n');
        alloyModel += ("pre_" + transition.modifiedName + "[s]" + '\n');
        alloyModel += ("semantics_" + transition.modifiedName + "[s, s']" + '\n');

        alloyModel += "}\n\n";
    }

    static void printSemantics(DashTrans transition, DashModule module) {
        alloyModel += ("pred semantics_" + transition.modifiedName + "[s, s': Snapshot] {" + '\n');

        if (!module.stateHierarchy)
            alloyModel += ("s'.taken = " + transition.modifiedName + '\n');

        if (module.stateHierarchy) {
            alloyModel += ("s.stable = True => {\n");
            alloyModel += ("s'.taken = " + transition.modifiedName + "\n");

            alloyModel += ("} else {\n");
            alloyModel += ("no {_s.taken + t} & {\n");
            for (DashTrans trans : module.transitions.values()) {
                if (getParentConcState(trans.parentState).modifiedName.equals(getParentConcState(transition.parentState).modifiedName))
                    alloyModel += (trans.modifiedName + " + \n");
            }
            alloyModel += ("}\n");
            alloyModel += ("}\n");
        }
        alloyModel += "}\n\n";
    }

    static void printEnabledNextStepPred(DashTrans transition, DashModule module) {
        alloyModel += ("pred enabledAfterStep_" + transition.modifiedName + "[_s, s: Snapshot] {" + '\n');

        printPreCondition(transition, module, true);

        alloyModel += ("s.stable = True => {\n");
        alloyModel += ("no t & {\n");
        for (DashTrans trans : module.transitions.values()) {
            if (getParentConcState(trans.parentState).modifiedName.equals(getParentConcState(transition.parentState).modifiedName))
                alloyModel += (trans.modifiedName + " + \n");
        }
        alloyModel += ("} else {\n");
        alloyModel += ("no {_s.taken + t} & {\n");
        for (DashTrans trans : module.transitions.values()) {
            if (getParentConcState(trans.parentState).modifiedName.equals(getParentConcState(transition.parentState).modifiedName))
                alloyModel += (trans.modifiedName + " + \n");
        }
        alloyModel += ("}\n");
        alloyModel += ("}\n");

        alloyModel += "}\n\n";
    }

    static void printModelDefinition(DashModule module) {
        alloyModel += ("/***************************** MODEL DEFINITION *******************************/\n\n");

        printOperation(module);

        alloyModel += ("pred small_step[s, s': Snapshot] {\n" + "operation[s, s']\n" + "}\n");

        if (module.stateHierarchy)
            printTestIfNextStable(module);

        if (module.stateHierarchy)
            printIsEnabledPred(module);

        printEqualsPred(module);

        if (module.stateHierarchy)
            alloyModel += ("fact {\n" + "all s: Snapshot | s in initial iff init[s]]\n" + "all s, s': Snapshot | s->s' in nextStep iff small_step[s, s']]\n" + "all s, s': Snapshot | equals[s, s'] => s = s'\n" + "all s: Snapshot | (isEnabled[s] && no s': Snapshot | small_step[s, s']) => s.stable = False\n" + " all s: Snapshot | s.stable = False => some s.nextStep\n" + "path" + "}\n");
        if (!module.stateHierarchy)
            alloyModel += ("fact {\n" + "all s: Snapshot | s in initial iff init[s]]\n" + "all s, s': Snapshot | s->s' in nextStep iff small_step[s, s']]\n" + "all s, s': Snapshot | equals[s, s'] => s = s'" + "path" + "}\n");

        alloyModel += "}\n\n";

        alloyModel += ("pred path {\n" + "all s:Snapshot, s': s.next | operation[s, s']\n" + "init[first]\n" + "}\n\n");
    }

    static void printOperation(DashModule module) {

        alloyModel += ("pred operation[s, s': Snapshot] {\n");

        for (String key : module.transitions.keySet())
            alloyModel += (key + "[s, s'] or \n");

        alloyModel += "}\n\n";
    }

    static void printTestIfNextStable(DashModule module) {

        alloyModel += ("pred testIfNextStable[s, s': Snapshot, genEvents: set InternalEvent, t:TransitionLabel] {\n");

        for (String key : module.transitions.keySet())
            alloyModel += ("!enabledAfterStep_" + key + "[s, s', t, genEvents]\n");

        alloyModel += "}\n\n";
    }

    static void printIsEnabledPred(DashModule module) {

        alloyModel += ("pred isEnabled[s: Snapshot] {\n");

        for (String key : module.transitions.keySet())
            alloyModel += ("pre_" + key + "[s] or\n");

        alloyModel += "}\n\n";
    }

    static void printEqualsPred(DashModule module) {
        alloyModel += ("pred equals[s, s': Snapshot] {\n");
        alloyModel += ("s'.conf = s.conf \n");
        alloyModel += ("s'.events = s.events \n");
        alloyModel += ("s'.taken = s.taken {\n");

        alloyModel += ("// Model specific declarations\n");

        for (String key : module.variableNames.keySet()) {
            for (String var : module.variableNames.get(key))
                alloyModel += ("s'." + key + "_" + var + " = s." + key + "_" + var + '\n');
        }

        alloyModel += "}\n\n";
    }

    static void printInitalCond(DashModule module) {
        alloyModel += "/****************************** INITIAL CONDITIONS ****************************/\n\n";

        alloyModel += "pred init[s: Snapshot] {";

        alloyModel += "s.conf = {\n";
        for (DashState state : module.defaultStates)
            alloyModel += state.modifiedName + " + ";
        for (DashConcState concState : module.concStates.values()) {
            if (concState.states.size() == 0)
                alloyModel += concState.modifiedName + " + ";
        }
        alloyModel += "\n}\n";

        alloyModel += ("no s.taken \n");
        alloyModel += ("no s.events & InternalEvent \n");

        alloyModel += ("// Model Specific Constraints \n");

        for (DashInit init : module.initConditions) {
            for (Expr expr : init.exprList)
                alloyModel += (modifyExprVariables(expr, init.parent, module) + '\n');
        }
        alloyModel += "}\n";
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

    //Take an expression in a do statement and modify any variables present. Eg: active_players should become
    //s.Game_active_players
    static String modifyExprVariables(Expr expr, DashConcState parent, DashModule module) {
        final List<String> variablesInParent = module.variableNames.get(parent.modifiedName);
        String expression = expr.toString();

        DashConcState outerConcState = parent.parent;

        expression = getModifiedExpr(expression, parent, expr, variablesInParent);

        while (outerConcState != null) {
            expression = getModifiedExpr(expression, outerConcState, expr, module.variableNames.get(outerConcState.modifiedName));
            outerConcState = outerConcState.parent;
        }

        return expression;
    }

    static String getModifiedExpr(String expression, DashConcState parent, Expr expr, List<String> exprList) {
        if (exprList == null)
            return expression;

        if (expr instanceof ExprQt)
            expression = getQuantifiedExpression((ExprQt) expr);

        for (String var : exprList)
            expression = splitChangeExpr(var, (Arrays.asList(expression.split(" "))), parent);

        return expression;
    }

    static String splitChangeExpr(String var, List<String> exprList, DashConcState parent) {
        String expression = "";

        for (String expr : exprList) {
            //if (expr.contains(".") && !expr.contains("s."))
            //expr = (expr.substring(expr.indexOf(".") + 1) + "[" + expr.substring(0, expr.indexOf(".")) + "]");
            if (expr.contains(var + "'"))
                expression += (expr.replace((var + "'"), ("s'." + parent.modifiedName + '_' + var)) + " ");
            else if (expr.contains(var))
                expression += (expr.replace((var), ("s." + parent.modifiedName + '_' + var)) + " ");
            else
                expression += (expr + " ");
        }

        return expression;
    }

    // Quantified expressions do not form correctly when using the .toString() function. Therefore, we need to break
    //down quantified expressions ourselves and convert them to a string
    static String getQuantifiedExpression(ExprQt expr) {
        String expression = "";

        for (Decl decl : expr.decls) {
            for (ExprHasName declName : decl.names)
                expression += (declName.toString() + ", ");
            expression = expression.substring(0, expression.length() - 2); // Remove the leading comma
            expression += (" : " + decl.expr + ", ");
        }
        expression = expression.substring(0, expression.length() - 2); // Remove the leading comma
        expression += (" | " + expr.sub.toString());

        return expression;
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

}
