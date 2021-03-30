package edu.mit.csail.sdg.parser;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import edu.mit.csail.sdg.ast.DashAction;
import edu.mit.csail.sdg.ast.DashConcState;
import edu.mit.csail.sdg.ast.DashCondition;
import edu.mit.csail.sdg.ast.DashDoExpr;
import edu.mit.csail.sdg.ast.DashFrom;
import edu.mit.csail.sdg.ast.DashGoto;
import edu.mit.csail.sdg.ast.DashOn;
import edu.mit.csail.sdg.ast.DashSend;
import edu.mit.csail.sdg.ast.DashState;
import edu.mit.csail.sdg.ast.DashTrans;
import edu.mit.csail.sdg.ast.DashWhenExpr;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;

public class TransformCoreDash {

    static List<DashTrans> transitions = new ArrayList<DashTrans>();

    public static void transformToCoreDash(DashModule module) throws IOException {
        modifyTransitions(module);
        CoreDashGenerator.printCoreDash(module);
        PrintAlloy.printAlloyModel(module);
    }

    static void modifyTransitions(DashModule module) {
        for (DashTrans trans : module.transitions.values()) {
            trans.fromExpr = new DashFrom(completeFromCommand(trans), false);
            trans.gotoExpr = new DashGoto(completeGoToCommand(trans));
            trans.onExpr = new DashOn(null, completeOnCommand(trans, module));
            trans.sendExpr = new DashSend(null, completeSendCommand(trans, module));
            trans.doExpr = addAction(trans.doExpr, module);
            trans.whenExpr = addCondition(trans.whenExpr, module);
        }
    }

    static void generateTransitions(Map<String,DashTrans> transitionList) {
        for (DashTrans trans : transitionList.values()) {
            if (trans.fromExpr.fromExpr.size() > 1) {
                for (String fromCommand : trans.fromExpr.fromExpr) {
                    DashTrans genTrans = new DashTrans(trans);
                    genTrans.fromExpr = new DashFrom(fromCommand, false);
                    transitions.add(genTrans);
                }
            } else {
                transitions.add(trans);
            }
        }
    }

    static DashDoExpr addAction(DashDoExpr doExpr, DashModule module) {
        if (doExpr != null) {
            if (doExpr.expr instanceof ExprUnary) {
                ExprUnary parentExprUnary = (ExprUnary) doExpr.expr;
                if (parentExprUnary.sub instanceof ExprList) {
                    ExprList exprList = (ExprList) parentExprUnary.sub;
                    for (Expr expression : exprList.args) {
                        if (expression instanceof ExprVar)
                            doExpr.exprList.add(getActionExpr(expression, module));
                        else
                            doExpr.exprList.add(expression);

                    }
                } else if (parentExprUnary.sub instanceof ExprVar)
                    doExpr.exprList.add(getActionExpr(parentExprUnary.sub, module));
                else
                    doExpr.exprList.add(parentExprUnary.sub);
            } else {
                doExpr.exprList.add(doExpr.expr);
            }
        }
        return doExpr;
    }

    static DashWhenExpr addCondition(DashWhenExpr whenExpr, DashModule module) {
        if (whenExpr != null) {
            if (whenExpr.expr instanceof ExprUnary) {
                ExprUnary parentExprUnary = (ExprUnary) whenExpr.expr;
                if (parentExprUnary.sub instanceof ExprList) {
                    ExprList exprList = (ExprList) parentExprUnary.sub;
                    for (Expr expression : exprList.args) {
                        if (expression instanceof ExprVar) {
                            whenExpr.exprList.add(getActionExpr(expression, module));
                        } else {
                            whenExpr.exprList.add(expression);
                        }
                    }
                } else if (parentExprUnary.sub instanceof ExprVar)
                    whenExpr.exprList.add(getConditionExpr(parentExprUnary.sub, module));
                else
                    whenExpr.exprList.add(parentExprUnary.sub);
            } else {
                whenExpr.exprList.add(whenExpr.expr);
            }
        }
        return whenExpr;
    }

    static Expr getActionExpr(Expr expr, DashModule module) {
        for (DashAction value : module.actions.values()) {
            if (expr.toString().equals(value.name))
                return value.expr;
        }
        return expr;
    }

    static Expr getConditionExpr(Expr expr, DashModule module) {
        for (DashCondition value : module.conditions.values()) {
            if (expr.toString().equals(value.name))
                return value.expr;
        }
        return expr;
    }

    static String completeOnCommand(DashTrans trans, DashModule module) {
        if (trans.onExpr == null)
            return null;

        String onCommand = trans.onExpr.name;
        String eventParent = "";
        Object eventParentObj = trans.parentState;

        if (onCommand.contains("/")) {
            eventParent = onCommand.substring(0, onCommand.indexOf('/'));
            onCommand = onCommand.substring(onCommand.indexOf('/') + 1);
        }

        while (eventParentObj != null) {
            if (eventParentObj instanceof DashConcState)
                onCommand = (((DashConcState) eventParentObj).name + "_" + onCommand);

            eventParentObj = getParent(eventParentObj);
        }

        return onCommand;
    }

    static String completeSendCommand(DashTrans trans, DashModule module) {
        if (trans.sendExpr == null)
            return null;

        String sendCommand = trans.sendExpr.name;
        String eventParent = "";
        Object eventParentObj = trans.parentState;

        if (sendCommand != null && sendCommand.contains("/")) {
            eventParent = sendCommand.substring(0, sendCommand.indexOf('/'));
            sendCommand = sendCommand.substring(sendCommand.indexOf('/') + 1);
        }

        while (eventParentObj != null) {
            if (eventParentObj instanceof DashConcState)
                sendCommand = (((DashConcState) eventParentObj).name + "_" + sendCommand);

            eventParentObj = getParent(eventParentObj);
        }

        return sendCommand;
    }

    static List<String> completeFromCommand(DashTrans trans) {
        List<String> completedFromCommands = new ArrayList<String>();

        if (trans.fromExpr != null) {
            for (String fromCommand : trans.fromExpr.fromExpr) {
                completedFromCommands.add(generateCompleteCommand(trans, fromCommand));
            }
        } else {
            completedFromCommands.add(generateCompleteCommand(trans, ""));
        }


        return completedFromCommands;
    }

    static List<String> completeGoToCommand(DashTrans trans) {
        List<String> completedGoToCommands = new ArrayList<String>();

        if (trans.gotoExpr != null) {
            for (String gotoCommand : trans.gotoExpr.gotoExpr) {
                if (trans.parentState instanceof DashConcState)
                    completedGoToCommands.add(generateCompleteCommand(trans, gotoCommand));
                if (trans.parentState instanceof DashState)
                    completedGoToCommands.add(generateCompleteCommand(trans.parentState, gotoCommand));
            }
        } else {
            completedGoToCommands.add(generateCompleteCommand(trans, ""));
        }

        return completedGoToCommands;
    }

    static String generateCompleteCommand(Object transItem, String fromExpr) {
        String completeCommand = "";
        Object parentObject = null;

        if (transItem instanceof DashTrans)
            parentObject = ((DashTrans) transItem).parentState;
        if (transItem instanceof DashState)
            parentObject = ((DashState) transItem).parent;
        if (transItem instanceof DashConcState)
            parentObject = ((DashConcState) transItem).parent;

        while (parentObject != null) {
            if (parentObject instanceof DashConcState) {
                completeCommand = ((DashConcState) parentObject).name + "/" + completeCommand;
                parentObject = getParent(parentObject);
            } else if (parentObject instanceof DashState) {
                completeCommand = ((DashState) parentObject).name + "/" + completeCommand;
                parentObject = getParent(parentObject);
            }
        }

        completeCommand = completeCommand + fromExpr;

        if (completeCommand.substring(completeCommand.length() - 1).equals("/")) // If the last character is a /, then remove it
            completeCommand = completeCommand.substring(0, completeCommand.length() - 1);


        return completeCommand;
    }

    static Object getParent(Object parent) {
        if (parent instanceof DashState)
            return ((DashState) parent).parent;
        if (parent instanceof DashConcState)
            return ((DashConcState) parent).parent;
        return null;
    }

}
