package edu.mit.csail.sdg.parser;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import edu.mit.csail.sdg.ast.DashAction;
import edu.mit.csail.sdg.ast.DashConcState;
import edu.mit.csail.sdg.ast.DashCondition;
import edu.mit.csail.sdg.ast.DashDoExpr;
import edu.mit.csail.sdg.ast.DashEvent;
import edu.mit.csail.sdg.ast.DashFrom;
import edu.mit.csail.sdg.ast.DashGoto;
import edu.mit.csail.sdg.ast.DashOn;
import edu.mit.csail.sdg.ast.DashSend;
import edu.mit.csail.sdg.ast.DashState;
import edu.mit.csail.sdg.ast.DashTemplateCall;
import edu.mit.csail.sdg.ast.DashTrans;
import edu.mit.csail.sdg.ast.DashTransTemplate;
import edu.mit.csail.sdg.ast.DashWhenExpr;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;

public class DashToCoreDash {

    static int transitionCount = 0;

    public static void transformToCoreDash(DashModule module) throws IOException {
        transitionCount = 0;
        getAllTransitions(module);
        modifyTransitions(module);
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

    /* Fetch all the transitions in the model */
    static void getAllTransitions(DashModule module) {
        for (DashConcState concState : module.concStates.values()) {
            for (DashTrans transition : concState.transitions)
                addTrans(concState, transition, module);
            for (DashTemplateCall templateCall : concState.templateCall)
                addTemplateCall(concState, templateCall, module);
        }

        for (DashState state : module.states.values()) {
            for (DashTrans transition : state.transitions)
                addTrans(state, transition, module);
        }
    }

    /*
     * This is called by the getAllTransitions function once it finds a transition
     * inside an OR state
     */
    public static void addTrans(DashState parent, DashTrans transition, DashModule module) {
        String modifiedTransName = parent.modifiedName + '_' + transition.name;
        transition.modifiedName = modifiedTransName;
        transition.parentState = parent;

        /*
         * If we have more than one from command (source), split up the transition such
         * that each transition represents one from command.
         */
        if (transition.fromExpr != null && transition.fromExpr.fromExpr.size() > 0) {
            for (String fromExpr : transition.fromExpr.fromExpr) {
                if (transition.name == null)
                    modifiedTransName = parent.modifiedName + "_t_" + (++transitionCount);
                generateTransition(transition, fromExpr, modifiedTransName, module);
            }
        } else {
            if (transition.name == null)
                modifiedTransName = parent.modifiedName + "_t_" + (++transitionCount);
            transition.modifiedName = modifiedTransName;
            module.transitions.put(modifiedTransName, transition);
        }
    }

    /*
     * This is called by the getAllTransitions function once it finds a transition
     * inside an conc state
     */
    public static void addTrans(DashConcState parent, DashTrans transition, DashModule module) {
        String modifiedTransName = parent.modifiedName + '_' + transition.name;
        transition.modifiedName = modifiedTransName;
        transition.parentState = parent;

        /*
         * If we have more than one from command (source), split up the transition such
         * that each transition represents one from command.
         */
        if (transition.fromExpr != null && transition.fromExpr.fromExpr.size() > 0) {
            for (String fromExpr : transition.fromExpr.fromExpr) {
                if (transition.name == null)
                    modifiedTransName = parent.modifiedName + "_t_" + (++transitionCount);
                generateTransition(transition, fromExpr, modifiedTransName, module);
            }
        } else {
            if (transition.name == null)
                modifiedTransName = parent.modifiedName + "_t_" + (++transitionCount);
            transition.modifiedName = modifiedTransName;
            module.transitions.put(modifiedTransName, transition);
        }
    }

    /*
     * This is called by the addConcState function once it finds a transition
     * template call. It refers to the template being called and uses it to create
     * new transitions
     */
    public static void addTemplateCall(DashConcState parent, DashTemplateCall templateCall, DashModule module) {
        DashTransTemplate transTemplate = module.transitionTemplates.get(templateCall.templateName);
        List<String> declNames = new ArrayList<String>();
        int count = 0;

        //Each decl is an argument for a template call
        for (Decl decl : transTemplate.decls) {
            declNames.add(decl.get().toString());
        }

        DashTrans trans = new DashTrans(null, templateCall.name, new ArrayList<Object>());
        trans.parentState = parent;

        //If we have an On command, check if it matches an argument. If it does, then set the on Command
        //to that of the argument
        if (transTemplate.onExpr != null) {
            if (declNames.indexOf(transTemplate.onExpr.name) != -1)
                trans.onExpr = new DashOn(null, templateCall.templateParam.get(declNames.indexOf(transTemplate.onExpr.name)));
            else
                trans.onExpr = new DashOn(null, transTemplate.onExpr.name);
        }

        //If we have a From command, check if it matches an argument. If it does, then set the From Command
        //to that of the argument
        if (transTemplate.fromExpr != null && !transTemplate.fromExpr.fromAll) {
            List<String> fromExprList = new ArrayList<String>();

            for (String fromExpr : transTemplate.fromExpr.fromExpr) {
                if (declNames.indexOf(fromExpr) != -1)
                    fromExprList.add(templateCall.templateParam.get(declNames.indexOf(fromExpr)));
                else
                    fromExprList.add(fromExpr);
            }
            trans.fromExpr = new DashFrom(fromExprList, false);
        }

        //If we have a Goto command, check if it matches an argument. If it does, then set the Goto Command
        //to that of the argument
        if (transTemplate.gotoExpr != null) {
            if (declNames.indexOf(transTemplate.gotoExpr.gotoExpr.get(0)) != -1)
                trans.gotoExpr = new DashGoto(templateCall.templateParam.get(declNames.indexOf(transTemplate.gotoExpr.gotoExpr.get(0))));
            else
                trans.gotoExpr = new DashGoto(transTemplate.gotoExpr.gotoExpr);
        }

        //If we have a Send command, check if it matches an argument. If it does, then set the Send Command
        //to that of the argument
        if (transTemplate.sendExpr != null) {
            if (declNames.indexOf(transTemplate.sendExpr.name) != -1)
                trans.sendExpr = new DashSend(null, templateCall.templateParam.get(declNames.indexOf(transTemplate.sendExpr.name)));
            else
                trans.sendExpr = new DashSend(null, transTemplate.sendExpr.name);
        }

        //If we have a do command, add it to our transition
        if (transTemplate.doExpr != null) {
            trans.doExpr = new DashDoExpr(null, transTemplate.doExpr.expr);
        }

        //If we have a when command, add it to our transition
        if (transTemplate.whenExpr != null) {
            trans.whenExpr = new DashWhenExpr(null, transTemplate.whenExpr.expr);
        }

        //If the from command is: from *, then we need to fetch all the Or states in the conc state,
        //and create new transitions each with a different or state as the source
        if (transTemplate.fromExpr != null && transTemplate.fromExpr.fromAll) {
            for (DashState state : parent.states) {
                trans.fromExpr = new DashFrom(state.name, false);
                trans.modifiedName = parent.modifiedName + "_" + templateCall.name + "__" + (++transitionCount);
                //System.out.println("Trans Name: " + trans.modifiedName + " From: " + trans.fromExpr.fromExpr.get(0));
                module.transitions.put(trans.modifiedName, new DashTrans(trans));
            }
        } //If we have more than one From command, create a new transition for each for command
        else if (transTemplate.fromExpr != null && trans.fromExpr.fromExpr.size() > 0) {
            for (String fromExpr : trans.fromExpr.fromExpr)
                generateTransition(trans, fromExpr, parent.modifiedName + "_" + templateCall.name + "__" + (++transitionCount), module);
        } else {
            trans.modifiedName = parent.modifiedName + "_" + templateCall.name + "__" + (++transitionCount);
            module.transitions.put(trans.modifiedName, trans);
        }

    }

    static void generateTransition(DashTrans transition, String fromExpr, String modifiedName, DashModule module) {
        DashTrans trans = new DashTrans(transition); // New transition representing one of the From commands
        trans.fromExpr = new DashFrom(fromExpr, false); // Add the from command to the new transition
        trans.modifiedName = modifiedName;
        module.transitions.put(modifiedName, trans);
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
            if (eventParentObj instanceof DashConcState) {
                for (DashEvent event : ((DashConcState) eventParentObj).events) {
                    if (event.name.equals(onCommand))
                        onCommand = (((DashConcState) eventParentObj).name + "_" + onCommand);
                }
            }

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
