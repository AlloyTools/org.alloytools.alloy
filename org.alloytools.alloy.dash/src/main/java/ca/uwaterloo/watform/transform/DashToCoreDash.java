package ca.uwaterloo.watform.transform;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import ca.uwaterloo.watform.ast.DashAction;
import ca.uwaterloo.watform.ast.DashConcState;
import ca.uwaterloo.watform.ast.DashCondition;
import ca.uwaterloo.watform.ast.DashDoExpr;
import ca.uwaterloo.watform.ast.DashEvent;
import ca.uwaterloo.watform.ast.DashFrom;
import ca.uwaterloo.watform.ast.DashGoto;
import ca.uwaterloo.watform.ast.DashOn;
import ca.uwaterloo.watform.ast.DashSend;
import ca.uwaterloo.watform.ast.DashState;
import ca.uwaterloo.watform.ast.DashTemplateCall;
import ca.uwaterloo.watform.ast.DashTrans;
import ca.uwaterloo.watform.ast.DashTransTemplate;
import ca.uwaterloo.watform.ast.DashWhenExpr;
import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.parser.DashValidation;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;

public class DashToCoreDash {

    static int transitionCount = 0;

    public static DashModule transformToCoreDash(DashModule module) throws IOException {
        transitionCount = 0;
        getAllTransitions(module);
        modifyTransitions(module);
        modifyGoToCommands(module);   
        modifyTransitionParent(module); 
        return module;
    }

    static void modifyTransitions(DashModule module) {
        for (DashTrans trans : module.transitions.values()) {
            trans.fromExpr = new DashFrom(completeFromCommand(trans, module), false);
            trans.gotoExpr = new DashGoto(completeGoToCommand(trans, module));
            trans.onExpr = new DashOn(null, completeOnCommand(trans, module), checkInternalEvent(trans, module));
            trans.sendExpr = new DashSend(null, completeSendCommand(trans, module));
            trans.doExpr = addAction(trans.doExpr, module);
            trans.whenExpr = addCondition(trans.whenExpr, module);
        }
    }
    
    /* Check the source state of a transition, and set that source state as its parent. Simplifies the 
     * CoreDash to Alloy AST conversion. Then add this transition to the list of transitions for that state */
    static void modifyTransitionParent(DashModule module) {
        for (DashTrans trans : module.transitions.values()) {
        	DashState sourceState = getStateFromName(trans.fromExpr.fromExpr.get(0).replace("/", "_"), module);
       	
        	if(sourceState != null) {
        		trans.parentState = sourceState;
        		
        		for(DashState state: module.states.values()) {
        			if(state.modifiedName.equals(sourceState.modifiedName))
        				state.modifiedTransitions.add(trans);
        		}
        	}     	
        }
    }  
    
    /* Check if a GoTo command transitions to a state that has inner OR states. If so,
     * then that transition will need to transition to the default inner OR state */
    static void modifyGoToCommands(DashModule module) {
        for (DashTrans trans : module.transitions.values()) {
        	DashState destinationState = getStateFromName(trans.gotoExpr.gotoExpr.get(0), module);
        	
        	String defaultInnerState = "";
        	/* destState is null if the destination state is a concurrent state (it has no OR states) */
        	if(destinationState != null) {
        		defaultInnerState = getDefaultState(trans, destinationState);
        		trans.gotoExpr = new DashGoto(new ArrayList<String>(Arrays.asList(defaultInnerState)));
        	}     	
       
        }
    }
     
    //Check to see if a state that we are transitioning to has an inner default state,
    //if it does, then the transition will need to transition to that state instead
    static String getDefaultState(DashTrans trans, DashState state) { 
    	for(DashState innerState: state.states) {
    		if(innerState.isDefault)
    			return getDefaultState(trans, innerState);
    	}

        return state.modifiedName;
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
            transition.parentConcState = getParentConcState(parent);
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
            transition.parentConcState = parent;
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
                trans.onExpr = new DashOn(null, templateCall.templateParam.get(declNames.indexOf(transTemplate.onExpr.name)), checkInternalEvent(trans, module));
            else
                trans.onExpr = new DashOn(null, transTemplate.onExpr.name, checkInternalEvent(trans, module));
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
                trans.parentConcState = parent;
                module.transitions.put(trans.modifiedName, new DashTrans(trans));
            }
        } //If we have more than one From command, create a new transition for each for command
        else if (transTemplate.fromExpr != null && trans.fromExpr.fromExpr.size() > 0) {
            for (String fromExpr : trans.fromExpr.fromExpr)
                generateTransition(trans, fromExpr, parent.modifiedName + "_" + templateCall.name + "__" + (++transitionCount), module);
        } else {
            trans.modifiedName = parent.modifiedName + "_" + templateCall.name + "__" + (++transitionCount);
            trans.parentConcState = parent;
            module.transitions.put(trans.modifiedName, trans);
        }

    }

    static void generateTransition(DashTrans transition, String fromExpr, String modifiedName, DashModule module) {
        DashTrans trans = new DashTrans(transition); // New transition representing one of the From commands
        trans.fromExpr = new DashFrom(fromExpr, false); // Add the from command to the new transition
        trans.modifiedName = modifiedName;
        trans.parentConcState = getParentConcState(transition.parentState);
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

        if (onCommand.contains("/")) 
            onCommand = onCommand.substring(onCommand.indexOf('/') + 1);

        for(DashConcState concState: module.concStates.values()) {
        	for(DashEvent event: concState.events) {
        		if(event.name.equals(onCommand))
        			return (concState.modifiedName + "_" + onCommand);
        	}
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
            if (eventParentObj instanceof DashConcState) {
            	if (checkForEvent((DashConcState) eventParentObj, sendCommand))
            		return ((DashConcState) eventParentObj).modifiedName + "_" + sendCommand;
            }

            eventParentObj = getParent(eventParentObj);
        }
        
        return sendCommand;
    }
    
    static Boolean checkInternalEvent(DashTrans trans, DashModule module)
    {
        if (trans.onExpr == null)
            return false;
    	
        String onCommand = trans.onExpr.name;

        if (onCommand.contains("/")) 
            onCommand = onCommand.substring(onCommand.lastIndexOf('/') + 1);

        for(DashConcState concState: module.concStates.values()) {
        	for(DashEvent event: concState.events) {
        		if(event.type.equals("event") && event.name.equals(onCommand)) {
        			return true;
        		}
        	}
        }  
        return false;
    }
    
    static Boolean checkForEvent(DashConcState concState, String eventName) {
    	for (DashEvent event: concState.events) {
    		if (event.name.equals(eventName)) 
    			return true;
    		
    	}
    	return false;
    }

    static List<String> completeFromCommand(DashTrans trans, DashModule module) {
        List<String> completedFromCommands = new ArrayList<String>();

        if (trans.fromExpr != null) {
            for (String fromCommand : trans.fromExpr.fromExpr) {
            	if(fromCommand.contains("/"))
            		fromCommand = fromCommand.substring(fromCommand.lastIndexOf("/") + 1);
            	
            	DashState fromState = locateState(trans, fromCommand, module);
            	
            	if(fromState != null)
            		completedFromCommands.add(fromState.modifiedName);
            	else /* Transitioning to a conc state that does not have an OR state */
            		completedFromCommands.add(generateCompleteCommand(trans, fromCommand));
            }
        } else {
            completedFromCommands.add(generateCompleteCommand(trans, ""));
        }
        
        return completedFromCommands;
    }

    static List<String> completeGoToCommand(DashTrans trans, DashModule module) {
        List<String> completedGoToCommands = new ArrayList<String>();

        if (trans.gotoExpr != null) {
            for (String gotoCommand : trans.gotoExpr.gotoExpr) {
            	if(gotoCommand.contains("/"))
            		gotoCommand = gotoCommand.substring(gotoCommand.lastIndexOf("/") + 1);
            	
            	DashState gotoState = locateState(trans, gotoCommand, module);
            	
            	if(gotoState != null) {
            		completedGoToCommands.add(gotoState.modifiedName);
            	}
            	else /* Transitioning to a conc state that does not have an OR state */
            		completedGoToCommands.add(generateCompleteCommand(trans, gotoCommand));
            }
        }
        else {
            //If we do not have a goto command, it should be equal to the origin of the transition
            completedGoToCommands.add(trans.fromExpr.fromExpr.get(0));
        }
           
        return completedGoToCommands;
    }
    
    /* Locate an or state to transition to  */
    static DashState locateState(DashTrans trans, String command, DashModule module) {
    	DashConcState parent = getParentConcState(trans.parentState);
    	List<DashState> states = new ArrayList<DashState>();
    	
    	while(parent != null) {
    		for(DashState state: parent.states) {
    			states.add(state);
    			
    			if(state.states.size() > 0)
    				getInnerStates(state, states);
    		}
    		
    		for(DashState state: states) {
    			if(state.name.equals(command))
    				return state;
    		}
    		
    		parent = getParentConcState(parent.parent);
    	}
    	
    	return null;
    }
    
    static void getInnerStates(DashState state, List<DashState> states) {
		for(DashState innerState: state.states) {	
			states.add(innerState);
			
			if(innerState.states.size() > 0)
				getInnerStates(innerState, states);
		}
    }
    
    static String generateCompleteCommand(Object transItem, String expr) {
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

        completeCommand = completeCommand + expr;

        if (completeCommand.substring(completeCommand.length() - 1).equals("/")) // If the last character is a /, then remove it
            completeCommand = completeCommand.substring(0, completeCommand.length() - 1);
        
        return completeCommand;
    }
    
    static DashConcState getParentConcState(Object item) { 	
        if (item instanceof DashState) {
            if (((DashState) item).parent instanceof DashState)
                return getParentConcState(((DashState) item).parent);
            if (((DashState) item).parent instanceof DashConcState)
                return (DashConcState) ((DashState) item).parent;
        }

        if (item instanceof DashConcState)
            return (DashConcState) item;

        return null;
    }

    static Object getParent(Object parent) {
        if (parent instanceof DashState)
            return ((DashState) parent).parent;
        if (parent instanceof DashConcState)
            return ((DashConcState) parent).parent;
        return null;
    }
    
    static DashState getStateFromName(String stateName, DashModule module) {
    	for(DashState state: module.states.values()) {
    		if(state.modifiedName.equals(stateName))
    			return state;
    	}
    	return null;
    }
}