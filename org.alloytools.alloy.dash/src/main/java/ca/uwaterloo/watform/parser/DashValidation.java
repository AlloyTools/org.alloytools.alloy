package ca.uwaterloo.watform.parser;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4.Pos;
import ca.uwaterloo.watform.ast.DashAction;
import ca.uwaterloo.watform.ast.DashConcState;
import ca.uwaterloo.watform.ast.DashCondition;
import ca.uwaterloo.watform.ast.DashEvent;
import ca.uwaterloo.watform.ast.DashInit;
import ca.uwaterloo.watform.ast.DashInvariant;
import ca.uwaterloo.watform.ast.DashState;
import ca.uwaterloo.watform.ast.DashTrans;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBadJoin;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;

/**
 * This class represents is used to check for well-formedness conditions for a
 * parsed Dash model.
 *
 * The DashParser calls the validateDashModel function once it completes parsing
 * a concurrent state. It will iterate through the states, transitions, etc in
 * the conc state and store them in HashMaps for later use. Once the required
 * information is stored (state names, transition names, Alloy expressions,
 * etc), we will check for issues in the Dash model.
 *
 * The issues being checked for are (description of an issue: function name that
 * finds the issue)
 *
 * Two or more states with the same name with in the same level:
 * hasSameStateName
 *
 * Two or more transitions with the same name with in the same level:
 * hasSameTransName
 *
 * Two or more events with the same name with in the same conc state:
 * hasSameEventName
 *
 * Illegal transitions (check function for examples of illegal transitions):
 * hasLegalTransCommand
 *
 * Reference to a variable that does not exist in the concurrent state:
 * validateExprVar This requires us to break up an Alloy expression until we
 * reach a variable name (ExprVar)
 *
 * Conc States/States without a default state: hasDefaultState
 *
 * This class also parses an imported module such that we references to items in
 * an imported module are found to be legal references: importModule
 *
 **/
public class DashValidation {

    static DashConcState                   currentConcStateValidated;

    static int                             orStateCount           = 0;

    /*
     * A list of all the transitions in the DASH model. This is used for validation
     * purposes. This is accessed by Alloy.cup when parsing a transition.
     */
    static Map<String,List<DashTrans>>     transitions            = new LinkedHashMap<String,List<DashTrans>>();

    /*
     * A list of all the signature names in the DASH model. This is used for
     * validation purposes. This is accessed by Alloy.cup when parsing a signature.
     */
    static List<String>                    sigNames               = new ArrayList<String>();

    /*
     * A list of all the func and pred names in the DASH model. This is used for
     * validation purposes.
     */
    static List<String>                    funcNames              = new ArrayList<String>();

    /*
     * A list of all the concurrent state names in the DASH model. This is used for
     * validation purposes.
     */
    static List<String>                    concStateNames         = new ArrayList<String>();
    //A modified name is the name of a Dash item as it would appear in an Alloy model
    static List<String>                    concStateNamesModified = new ArrayList<String>();

    /*
     * A list of all the state names in the DASH model. This is used for validation
     * purposes.
     */
    public static Map<String,List<String>> stateNames             = new LinkedHashMap<String,List<String>>();

    /*
     * A list of all the event names in the DASH model. This is used for validation
     * purposes.
     */
    public static Map<String,List<String>> eventNames             = new LinkedHashMap<String,List<String>>();

    /*
     * A list of all the event names in the DASH model. This is used for validation
     * purposes. This is accessed by Alloy.cup when parsing an event.
     */
    public static Map<String,List<String>> transitionNames        = new LinkedHashMap<String,List<String>>();


    /*
     * A list of all the variable declarations in the DASH model. This is used for
     * validation purposes. declaration.
     */
    static List<Decl>                      declarations           = new ArrayList<Decl>();
    static Map<String,List<String>>        declarationNames       = new LinkedHashMap<String,List<String>>();

    /*
     * Store the quantifier variables in this container. Example: (all c: variable
     * |...) c would be the quantifer variable in this case
     */
    static List<String>                    quantifierVars         = new ArrayList<String>();

    /*
     * A list of all the expressions in the DASH model. This is used for validation
     * purposes. This is accessed by Alloy.cup when parsing an expression.
     */
    public static Map<String,List<Expr>>   expressions            = new LinkedHashMap<String,List<Expr>>();

    static List<String>                    keywords               = Arrays.asList("none", "no", "one", "some", "all");

    /*
     * Make sure that transitions declared are legal. An illegal transition would be
     * one that refers to an event that has not been declared, or attempts to make a
     * transition to a state that has not been declared, etc.
     */
    public static void hasLegalTransCommand(String concStateName) {
        for (DashTrans transition : transitions.get(concStateName)) {
            if (transition.onExpr != null) {
                validateTransRef(transition.onExpr.name, transition.onExpr.pos, eventNames.get(concStateName));
            }
            if (transition.gotoExpr != null) {
                for (String gotoName : transition.gotoExpr.gotoExpr) {
                    validateTransRef(gotoName, transition.gotoExpr.pos, stateNames.get(concStateName));
                }
            }
            if (transition.fromExpr != null) {
                for (String fromName : transition.fromExpr.fromExpr) {
                    validateTransRef(fromName, transition.fromExpr.pos, stateNames.get(concStateName));
                }
            }
            /*
             * if (transition.templateCall != null) { for (ExprVar arg :
             * transition.templateParam) { if
             * (!stateNames.get(concStateName).contains(arg.toString()) &&
             * !eventNames.get(concStateName).contains(arg.toString())) throw new
             * ErrorSyntax(arg.pos, "Could not resolve reference to: " + arg.toString()); }
             * }
             */
        }
    }

    /*
     * Check if a transition is referring to states/events that have been declared
     * in the current concurrent state
     */
    public static void validateTransRef(String ref, Pos pos, List<String> listToCompare) {
        int index = 0;
        if (ref.contains("/")) {
            index = ref.indexOf('/');
            if (!listToCompare.contains(ref.substring(index + 1)))
                throw new ErrorSyntax(pos, "Could not resolve reference to: " + ref.substring(index + 1));
            if (!concStateNames.contains(ref.substring(0, index)))
                throw new ErrorSyntax(pos, "Could not resolve reference to: " + ref.substring(0, index));
        } else {
            if (!listToCompare.contains(ref))
                throw new ErrorSyntax(pos, "Could not resolve reference to: " + ref);
        }
    }

    static void validateExprVar(DashConcState concState) {
        for (Expr expr : expressions.get(concState.modifiedName)) {

            ExprUnary parentExprUnary = null;

            if (expr instanceof ExprUnary) // Expressions inside do/when statements will be of type ExprUnary
                parentExprUnary = (ExprUnary) expr;

            //If we have multiple Alloy expressions, it will be stored as an ExprList object
            //and we will need to iterate through each of them and break them down until we
            //reach an object of type ExprVar (variable)
            if (parentExprUnary != null && parentExprUnary.sub instanceof ExprList) {
                ExprList exprList = (ExprList) parentExprUnary.sub;
                for (Expr expression : exprList.args) {
                    quantifierVars.clear(); //Clearly out previously stored quantified variables
                    getVarFromParentExpr(expression);
                }
            } else { //We only have on expression as opposed to multiple ones
                quantifierVars.clear();
                getVarFromParentExpr(expr);
            }
        }
    }

    private static String getVarFromParentExpr(Object parentExpr) {
        if (parentExpr instanceof ExprBinary) {
            ExprBinary exprBinary = (ExprBinary) parentExpr;
            getVarFromBinary(exprBinary);
        }

        if (parentExpr instanceof ExprUnary) {
            ExprUnary unary = (ExprUnary) parentExpr;
            getVarFromUnary(unary);
        }

        if (parentExpr instanceof ExprQt) {
            getVarFromExprQt((ExprQt) parentExpr);
        }

        if (parentExpr instanceof ExprVar) {
            checkIfVarValid((ExprVar) parentExpr);
        }

        return null;
    }

    /*
     * Breakdown a binary expression into its subcomponents Example of a binary
     * expression: #varible1 = #variable2
     */
    private static String getVarFromBinary(ExprBinary binary) {
        if (binary.left instanceof ExprUnary) {
            ExprUnary unary = (ExprUnary) binary.left;
            getVarFromUnary(unary);
            //return getVarFromUnary(unary);
        }

        if (binary.left instanceof ExprVar) {
            checkIfVarValid((ExprVar) binary.left);
        }

        if (binary.left instanceof ExprBinary) {
            getVarFromBinary((ExprBinary) binary.left);
        }

        if (binary.left instanceof ExprBadJoin) {
            getVarFromBadJoin((ExprBadJoin) binary.left);
        }

        if (binary.right instanceof ExprUnary) {
            ExprUnary unary = (ExprUnary) binary.right;
            getVarFromUnary(unary);
            //return getVarFromUnary(unary);
        }

        if (binary.right instanceof ExprVar) {
            checkIfVarValid((ExprVar) binary.right);
        }

        if (binary.right instanceof ExprBinary) {
            getVarFromBinary((ExprBinary) binary.right);
        }

        if (binary.right instanceof ExprBadJoin) {
            getVarFromBadJoin((ExprBadJoin) binary.right);
        }
        return null;
    }

    /*
     * Breakdown a unary expression into its subcomponents Example of an unary
     * expression: one varible
     */
    private static String getVarFromUnary(ExprUnary unary) {
        if (unary.sub instanceof ExprVar) {
            checkIfVarValid((ExprVar) unary.sub);
        }
        if (unary.sub instanceof ExprUnary) {
            getVarFromUnary((ExprUnary) unary.sub);
        }
        if (unary.sub instanceof ExprBadJoin) {
            getVarFromBadJoin((ExprBadJoin) unary.sub);
        }
        if (unary.sub instanceof ExprBinary) {
            getVarFromBinary((ExprBinary) unary.sub);
        }
        return null;
    }

    private static String getVarFromBadJoin(ExprBadJoin joinExpr) {
        if (joinExpr.left instanceof ExprVar) {
            checkIfVarValid((ExprVar) joinExpr.left);
        }
        if (joinExpr.left instanceof ExprUnary) {
            getVarFromUnary((ExprUnary) joinExpr.left);
        }
        if (joinExpr.left instanceof ExprBadJoin) {
            getVarFromBadJoin((ExprBadJoin) joinExpr.right);
        }
        if (joinExpr.right instanceof ExprVar) {
            checkIfVarValid((ExprVar) joinExpr.right);
        }
        if (joinExpr.right instanceof ExprUnary) {
            getVarFromUnary((ExprUnary) joinExpr.left);
        }
        if (joinExpr.right instanceof ExprBadJoin) {
            getVarFromBadJoin((ExprBadJoin) joinExpr.right);
        }
        return null;
    }

    /*
     * Breakdown a quantified expression into its subcomponents
     */
    private static String getVarFromExprQt(ExprQt exprQt) {
        getDeclsFromExprQT(exprQt);

        if (exprQt.sub instanceof ExprUnary) {
            getVarFromUnary((ExprUnary) exprQt.sub);
        }
        if (exprQt.sub instanceof ExprBinary) {
            getVarFromBinary((ExprBinary) exprQt.sub);
        }
        return null;
    }

    private static void getDeclsFromExprQT(ExprQt exprQt) {
        for (Decl decl : exprQt.decls) {
            quantifierVars.add(decl.get().toString());
            getVarFromParentExpr(decl.expr);
        }
    }

    private static void validateTransTemplateDecl(Pos pos, String concStateName, List<Decl> decls) {
        List<String> nameList;
        for (Decl decl : decls) {
            if (decl.expr instanceof ExprVar) {
                if (!decl.expr.toString().equals("State") && !decl.expr.toString().equals("Event"))
                    throw new ErrorSyntax(pos, "Expected Type: Abstract Boolean or Abstract Event or Abstract State");
            }
            if (decl.expr instanceof ExprVar && decl.expr.toString().equals("Event")) {
                nameList = new ArrayList<String>(eventNames.get(concStateName));
                nameList.add(decl.get().toString());
                eventNames.put(concStateName, nameList);
            }
            if (decl.expr instanceof ExprVar && decl.expr.toString().equals("State")) {
                nameList = new ArrayList<String>(stateNames.get(concStateName));
                nameList.add(decl.get().toString());
                stateNames.put(concStateName, nameList);
            }
        }
    }

    /*
     * Check if a variable found inside an Expression has been declared in the
     * current concurrent state
     */
    private static void checkIfVarValid(ExprVar var) {
        String variable = var.toString();
        String concStateToCheck = currentConcStateValidated.modifiedName;
        
        if (variable.contains("'"))
            variable = variable.replace("'", "");

        String concStateParName = "";
        if (currentConcStateValidated.parent != null)
            concStateParName = currentConcStateValidated.parent.modifiedName;
        else
            concStateParName = currentConcStateValidated.modifiedName;

        if (variable.contains("/")) {
        	concStateToCheck = variable.substring(0, variable.indexOf("/"));
        	variable = variable.substring(variable.indexOf("/") + 1);
        }
        
        if (!declarationNames.get(concStateToCheck).contains(variable) && !eventNames.get(concStateToCheck).contains(variable) && !declarationNames.get(concStateParName).contains(variable) && !keywords.contains(variable) && !quantifierVars.contains(variable) && !sigNames.contains(variable) && !funcNames.contains(variable)) {
            throw new ErrorSyntax(var.pos, "Could not resolve reference to: " + variable);
        }
    }

    /* Ensure that conc states have a default state */
    private static Boolean hasDefaultState(List<DashState> states) {
        orStateCount = 0;

        /*
         * There is no need to declare a default state if no states have been declared
         * inside a concurrent state
         */
        if (states.size() == 0)
            return true;

        for (DashState item : states) {
            if (item.isDefault)
                return true;
        }
        return false;
    }

    /* Ensure that conc states do not have orstates with the same name */
    private static void hasSameStateName(String name, List<DashState> states) {
        String stateName = "";
        String currentStateName = "";
        Boolean sameStateFound = false;

        for (DashState stateA : states) {
            stateName = stateA.name;
            for (DashState stateB : states) {
                if (stateName.equals(stateB.name) && sameStateFound)
                    throw new ErrorSyntax(stateB.pos, "This state has already been declared.");
                if (stateName.equals(stateB.name) && !sameStateFound)
                    sameStateFound = true;
            }
            sameStateFound = false;
        }
    }


    /* Ensure that conc states do not have orstates with the trans name */
    private static void hasSameTransName(String name, List<DashTrans> transitions) {
        String transName = "";
        String currentTransName = "";
        Boolean sameTransFound = false;

        for (DashTrans transA : transitions) {
            transName = transA.name;
            for (DashTrans transB : transitions) {
                if (transName != null && transB.name != null) {
                    if (transName.equals(transB.name) && sameTransFound)
                        throw new ErrorSyntax(transB.pos, "This transition has already been declared.");
                    if (transName.equals(transB.name) && !sameTransFound)
                        sameTransFound = true;
                }
            }
            sameTransFound = false;
        }
    }

    /* Ensure that conc states do not have events with the same name */
    private static void hasSameEventName(DashConcState concState) {
        String eventName = "";
        String currentEventName = "";
        Boolean sameEventFound = false;

        List<DashEvent> concStateEvent = getEvents(concState);

        for (DashEvent eventA : concStateEvent) {
            eventName = eventA.name;
            for (DashEvent eventB : concStateEvent) {
                if (eventName != null && eventB.name != null) {
                    if (eventName.equals(eventB.name) && sameEventFound)
                        throw new ErrorSyntax(eventB.pos, "This event has already been declared.");
                    if (eventName.equals(eventB.name) && !sameEventFound)
                        sameEventFound = true;
                }
            }
            sameEventFound = false;
        }
    }

    /* Accessed by the DashParser */
    public static void importModule(String fileName) {
    	System.out.println("File Name: " + fileName);
    	if(fileName.contains("/"))
    		fileName = fileName.substring(fileName.indexOf("/") + 1);
        File utilFolder = new File(DashOptions.dashModelLocation + "/util/" + fileName + ".als"); 
        if (utilFolder.exists()) {
            A4Reporter rep = new A4Reporter() {

                // For example, here we choose to display each "warning" by printing
                // it to System.out
                @Override
                public void warning(ErrorWarning msg) {
                    System.out.print("Relevance Warning:\n" + (msg.toString().trim()) + "\n\n");
                    System.out.flush();
                }
            };
            DashUtil.parseEverything_fromFileDash(rep, new LinkedHashMap<String,String>(), (DashOptions.dashModelLocation + "/util/" + fileName + ".als"));
        } else
            throw new ErrorSyntax("Could not import module: " + fileName);
    }

    /*
     * This function iterates through the concState hashmap and stores each
     * concurrent state name in the concStateNames list
     */
    public static void addConcStates(DashModule dashModule) {
        /* Get all the concurrent states */
        for (DashConcState concState : dashModule.concStates.values()) {
            concStateNames.add(concState.name);
            concStateNamesModified.add(concState.modifiedName);
        }

        for (String concStateName : concStateNamesModified)
            initializeNameContainers(concStateName, dashModule);

        /* Stores the names for each signature in the model */
        for (String sigName : dashModule.sigs.keySet()) {
            sigNames.add(sigName);
        }

    }

    //Get the set of event names inside the given Conc State
    public static List<DashEvent> getEvents(DashConcState parent) {
        List<DashEvent> events = new ArrayList<DashEvent>();

        for (DashEvent event : parent.events) {
            if (event.type.equals("env")) {
                //If we have an event such as env in_m1, in_m2: lone Patient, we
                //need to store in_m1 as an event and in_m2 as an Event
                for (Object name : event.decl.names) {
                    events.add(new DashEvent(event.pos, name.toString(), "env"));
                }
            } else {
                events.add(new DashEvent(event.pos, event.name, "event"));
            }
        }

        return events;
    }
    
    /* Store variables that have been declared in the concurrent state */
    static void readVariablesDeclared(String concStateName, DashModule module) 
    {
    	DashConcState concState = module.concStates.get(concStateName);
    	List<String> names = new ArrayList<String>();
    	
    	while (concState != null)
    	{
            /* Store the names of each variable inside decls in ConcState */
            for (Decl decl : concState.decls) {
                for (Object name : decl.names) 
                    names.add(name.toString());
            }
            
            concState = concState.parent;
    	}

        declarationNames.put(concStateName, new ArrayList<String>(names));
    }
    
    public static void getEventNames(String concStateName, DashModule dashModule)
    {
    	DashConcState concState = dashModule.concStates.get(concStateName);
    	List<String> names = new ArrayList<String>();
    	
    	while (concState != null)
    	{
            /* Stores the names for each event in the current conc state */
            for (DashEvent event : concState.events) {
                if (event.type.equals("env")) {
                    //If we have an event such as env in_m1, in_m2: lone Patient, we
                    //need to store in_m1, in_m2 as event names
                    for (Object name : event.decl.names) {
                        names.add(name.toString());
                    }
                } else {
                    names.add(event.name);
                }
            }
            
            concState = concState.parent;
    	}  
    	
    	eventNames.put(concStateName, new ArrayList<String>(names));
    }

    public static void initializeNameContainers(String concStateName, DashModule dashModule) {
        List<String> names = new ArrayList<String>();
        List<DashTrans> transitionList = new ArrayList<DashTrans>();
        List<Expr> expressionList = new ArrayList<Expr>();

        expressions.put(concStateName, expressionList);


        /* Stores the names for each state in the current conc state */
        for (DashState state : dashModule.concStates.get(concStateName).states) {
            getExprFromStateTrans(concStateName, state.modifiedName, dashModule);
            names.add(state.name);
        }

        stateNames.put(concStateName, new ArrayList<String>(names));
        names.clear();

        /* Stores the names for each action template in the current conc state */
        for (DashAction action : dashModule.concStates.get(concStateName).action)
            funcNames.add(action.name);
        
        /* Stores the names for each condition template in the current conc state */
        for (DashCondition condition : dashModule.concStates.get(concStateName).condition)
            funcNames.add(condition.name);
        
        /* Stores the names for each event in the current conc state */
        getEventNames(concStateName, dashModule);

        /* Stores the names for each variable in the current conc state */
        readVariablesDeclared(concStateName, dashModule);

        expressionList = new ArrayList<Expr>(expressions.get(concStateName));
        for (DashTrans trans : dashModule.concStates.get(concStateName).transitions) {
            names.add(trans.name);
            transitionList.add(trans);

            //The only kind of transition that will have declarations (decl) is a
            //transition template. Therefore, we will need to valdiate the arguments (decls)
            if (trans.transTemplate != null)
                validateTransTemplateDecl(trans.pos, concStateName, trans.transTemplate.decls);
            if (trans.doExpr != null) {
                expressionList.add(trans.doExpr.expr);
            }
            if (trans.whenExpr != null) {
                expressionList.add(trans.whenExpr.expr);
            }

        }
        expressions.put(concStateName, new ArrayList<Expr>(expressionList));
        transitions.put(concStateName, new ArrayList<DashTrans>(transitionList));
        transitionNames.put(concStateName, new ArrayList<String>(names));

        addExprFromConcState(dashModule.concStates.get(concStateName));
    }

    public static void getExprFromStateTrans(String concStateName, String stateName, DashModule dashModule) {
        List<Expr> expressionList = new ArrayList<Expr>(expressions.get(concStateName));

        /* Stores the names for each state in the current state */
        for (DashState state : dashModule.states.get(stateName).states) {
            getExprFromStateTrans(concStateName, state.modifiedName, dashModule);
        }

        for (DashTrans trans : dashModule.states.get(stateName).transitions) {
            //The only kind of transition that will have declarations (decl) is a
            //transition template. Therefore, we will need to valdiate the arguments (decls)
            if (trans.transTemplate != null)
                validateTransTemplateDecl(trans.pos, concStateName, trans.transTemplate.decls);
            if (trans.doExpr != null) {
                expressionList.add(trans.doExpr.expr);
            }
            if (trans.whenExpr != null) {
                expressionList.add(trans.whenExpr.expr);
            }
        }
        expressions.put(concStateName, expressionList);
    }

    public static void validateConcStates(DashModule dashModule) {
        for (String concStateName : concStateNamesModified) {
            DashConcState currentConcState = dashModule.concStates.get(concStateName);
            currentConcStateValidated = currentConcState;

            if (!hasDefaultState(currentConcState.states))
                throw new ErrorSyntax(dashModule.concStates.get(concStateName).pos, "A default state is required.");

            hasSameStateName(concStateName, currentConcState.states);
            hasSameTransName(concStateName, currentConcState.transitions);
            hasSameEventName(currentConcState);

            for (DashState state : currentConcState.states) {
                if (!hasDefaultState(state.states))
                    throw new ErrorSyntax(state.pos, "A default state is required.");

                hasSameStateName(concStateName, state.states);
                hasSameTransName(concStateName, state.transitions);
            }

            validateExprVar(dashModule.concStates.get(concStateName));
        }
    }

    public static void addExprFromConcState(DashConcState currentConcState) {

        List<Expr> localExpressions = new ArrayList<Expr>(expressions.get(currentConcState.modifiedName));

        if (currentConcState.init.size() > 0) {
            for (DashInit init : currentConcState.init)
                localExpressions.add(init.expr);
        }
        //if (currentConcState.invariant.size() > 0) {
        //    for (DashInvariant invariant : currentConcState.invariant)
                //localExpressions.add(invariant.expr);
        //}
        if (currentConcState.action.size() > 0) {
            for (DashAction action : currentConcState.action)
                localExpressions.add(action.expr);
        }
        if (currentConcState.condition.size() > 0) {
            for (DashCondition condition : currentConcState.condition)
                localExpressions.add(condition.expr);
        }
        expressions.put(currentConcState.modifiedName, new ArrayList<Expr>(localExpressions));
    }

    public static void validateDashModel(DashModule dashModule) {
        addConcStates(dashModule);
        validateConcStates(dashModule);
        clearContainers();
    }

    public static void clearContainers() {
        orStateCount = 0;
        concStateNames = new ArrayList<String>();
        concStateNamesModified = new ArrayList<String>();
        transitions = new HashMap<String,List<DashTrans>>();
        sigNames = new ArrayList<String>();
        funcNames = new ArrayList<String>();
        stateNames = new HashMap<String,List<String>>();
        eventNames = new HashMap<String,List<String>>();
        declarations = new ArrayList<Decl>();
        declarationNames = new HashMap<String,List<String>>();
        quantifierVars = new ArrayList<String>();
        expressions = new HashMap<String,List<Expr>>();
    }
}


