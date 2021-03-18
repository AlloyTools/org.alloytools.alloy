package edu.mit.csail.sdg.parser;

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
import edu.mit.csail.sdg.ast.ConcState;
import edu.mit.csail.sdg.ast.DashAction;
import edu.mit.csail.sdg.ast.DashCondition;
import edu.mit.csail.sdg.ast.DashInit;
import edu.mit.csail.sdg.ast.DashInvariant;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Event;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBadJoin;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.State;
import edu.mit.csail.sdg.ast.Trans;

/* Write comments to specify the checks and what functions they map to */
public class DASHValidation {

    static ConcState                       currentConcStateValidated;

    static int                             orStateCount           = 0;

    /*
     * A list of all the transitions in the DASH model. This is used for validation
     * purposes. This is accessed by Alloy.cup when parsing a transition.
     */
    static Map<String,List<Trans>>         transitions            = new LinkedHashMap<String,List<Trans>>();

    /*
     * A list of all the signature names in the DASH model. This is used for
     * validation purposes. This is accessed by Alloy.cup when parsing a signature.
     */
    static List<String>                    sigNames               = new ArrayList<String>();

    /*
     * A list of all the func and pred names in the DASH model. This is used for
     * validation purposes. This is accessed by Alloy.cup when parsing a signature.
     */
    static List<String>                    funcNames              = new ArrayList<String>();

    /*
     * A list of all the concurrent state names in the DASH model. This is used for
     * validation purposes. This is accessed by Alloy.cup when parsing a transition.
     */
    static List<String>                    concStateNames         = new ArrayList<String>();
    //A modified name is the name of a Dash item as it would appear in an Alloy model
    static List<String>                    concStateNamesModified = new ArrayList<String>();

    /*
     * A list of all the state names in the DASH model. This is used for validation
     * purposes. This is accessed by Alloy.cup when parsing a transition.
     */
    public static Map<String,List<String>> stateNames             = new LinkedHashMap<String,List<String>>();

    /*
     * A list of all the event names in the DASH model. This is used for validation
     * purposes. This is accessed by Alloy.cup when parsing an event.
     */
    public static Map<String,List<String>> eventNames             = new LinkedHashMap<String,List<String>>();


    /*
     * A list of all the variable declarations in the DASH model. This is used for
     * validation purposes. This is accessed by Alloy.cup when parsing a var
     * declaration.
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
        for (String name : stateNames.get(concStateName))
            System.out.println("State: " + name);
        for (String name : eventNames.get(concStateName))
            System.out.println("Event: " + name);

        for (Trans transition : transitions.get(concStateName)) {
            if (transition.onExpr != null) {
                validateTransRef(transition.onExpr.name, transition.onExpr.pos, eventNames.get(concStateName));
            }
            if (transition.gotoExpr != null) {
                for (String gotoName : transition.gotoExpr.gotoExpr) {
                    System.out.println("Checking :" + gotoName);
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

    /* Store variables that have been declared in the concurrent state */
    public static List<String> readVariablesDeclared(List<Decl> decls, List<String> names) {
        /* Store the names of each variable inside decls in ConcState */
        for (Decl decl : decls) {
            for (Object name : decl.names)
                names.add(name.toString());
        }
        return names;
    }


    public static void validateExprVar(ConcState concState) {
        for (Expr expr : expressions.get(concState.modifiedName)) {
            System.out.println("\nLooking at: " + expr.toString());

            ExprUnary parentExprUnary = null;

            if (expr instanceof ExprUnary) // Expressions inside do/when statements will be of type ExprUnary
                parentExprUnary = (ExprUnary) expr;

            //If we have multiple Alloy expressions, it will be stored as an ExprList object
            //and we will need to iterate through each of them and break them down until we
            //reach an object of type ExprVar (variable)
            if (parentExprUnary != null && parentExprUnary.sub instanceof ExprList) {
                ExprList exprList = (ExprList) parentExprUnary.sub;
                for (Expr expression : exprList.args) {
                    System.out.println("\nLooking at: " + expression.toString() + " Type: " + expression.getClass());
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
            System.out.println("ExprVar: " + parentExpr.toString());
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
            System.out.println("Left ExprVar: " + binary.left);
            checkIfVarValid((ExprVar) binary.left);
        }

        if (binary.left instanceof ExprBinary) {
            getVarFromBinary((ExprBinary) binary.right);
        }

        if (binary.left instanceof ExprBadJoin) {
            getVarFromBadJoin((ExprBadJoin) binary.right);
        }

        if (binary.right instanceof ExprUnary) {
            ExprUnary unary = (ExprUnary) binary.right;
            getVarFromUnary(unary);
            //return getVarFromUnary(unary);
        }

        if (binary.right instanceof ExprVar) {
            System.out.println("Right ExprVar: " + binary.right);
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
            System.out.println("ExprVar: " + unary.sub.toString());
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
            System.out.println("Left ExprVar: " + joinExpr.left.toString());
            checkIfVarValid((ExprVar) joinExpr.left);
        }
        if (joinExpr.left instanceof ExprUnary) {
            getVarFromUnary((ExprUnary) joinExpr.left);
        }
        if (joinExpr.left instanceof ExprBadJoin) {
            getVarFromBadJoin((ExprBadJoin) joinExpr.right);
        }
        if (joinExpr.right instanceof ExprVar) {
            System.out.println("Left ExprVar: " + joinExpr.right.toString());
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
            System.out.println("Var Name: " + decl.get());
            quantifierVars.add(decl.get().toString());
            getVarFromParentExpr(decl.expr);
        }
    }

    public static void validateTransTemplateDecl(Pos pos, String concStateName, List<Decl> decls) {
        List<String> nameList;
        for (Decl decl : decls) {
            if (decl.expr instanceof ExprVar) {
                System.out.println("Expr: " + decl.expr.toString());
                if (!decl.expr.toString().equals("State") && !decl.expr.toString().equals("Event"))
                    throw new ErrorSyntax(pos, "Expected Type: Abstract Boolean or Abstract Event or Abstract State");
            }
            if (decl.expr instanceof ExprVar && decl.expr.toString().equals("Event")) {
                System.out.println("Adding to Events: " + decl.get().toString());
                nameList = new ArrayList<String>(eventNames.get(concStateName));
                nameList.add(decl.get().toString());
                eventNames.put(concStateName, nameList);
            }
            if (decl.expr instanceof ExprVar && decl.expr.toString().equals("State")) {
                System.out.println("Adding to State: " + decl.get().toString());
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
        if (variable.contains("'"))
            variable = variable.replace("'", "");

        if (!declarationNames.get(currentConcStateValidated.modifiedName).contains(variable) && !keywords.contains(variable) && !quantifierVars.contains(variable) && !sigNames.contains(variable) && !funcNames.contains(variable)) {
            throw new ErrorSyntax(var.pos, "Could not resolve reference to: " + variable);
        }
    }

    /* Ensure that conc states have a default state */
    public static Boolean hasDefaultState(List<State> states) {
        orStateCount = 0;

        /*
         * There is no need to declare a default state if no states have been declared
         * inside a concurrent state
         */
        if (states.size() == 0)
            return true;

        for (State item : states) {
            if (item.isDefault)
                return true;
        }
        return false;
    }

    /* Ensure that conc states do not have orstates with the same name */
    public static void hasSameStateName(String name, List<State> states) {
        String stateName = "";
        String currentStateName = "";
        Boolean sameStateFound = false;

        for (State stateA : states) {
            stateName = stateA.name;
            for (State stateB : states) {
                if (stateName.equals(stateB.name) && sameStateFound)
                    throw new ErrorSyntax(stateB.pos, "This state has already been declared.");
                if (stateName.equals(stateB.name) && !sameStateFound)
                    sameStateFound = true;
            }
            sameStateFound = false;
        }
    }


    /* Ensure that conc states do not have orstates with the trans name */
    public static void hasSameTransName(String name, List<Trans> transitions) {
        String transName = "";
        String currentTransName = "";
        Boolean sameTransFound = false;

        for (Trans transA : transitions) {
            transName = transA.name;
            for (Trans transB : transitions) {
                if (transName.equals(transB.name) && sameTransFound)
                    throw new ErrorSyntax(transB.pos, "This transition has already been declared.");
                if (transName.equals(transB.name) && !sameTransFound)
                    sameTransFound = true;
            }
            sameTransFound = false;
        }
    }

    /* Ensure that conc states do not have events with the same name */
    public static void hasSameEventName(String name, List<Event> events) {
        String eventName = "";
        String currentEventName = "";
        Boolean sameEventFound = false;

        for (Event eventA : events) {
            eventName = eventA.name;
            for (Event eventB : events) {
                if (eventName.equals(eventB.name) && sameEventFound)
                    throw new ErrorSyntax(eventB.pos, "This event has already been declared.");
                if (eventName.equals(eventB.name) && !sameEventFound)
                    sameEventFound = true;
            }
            sameEventFound = false;
        }
    }

    public static void importModule(String fileName) {
        File utilFolder = new File(fileName + ".als");
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
            CompUtil.parseEverything_fromFileDash(rep, new LinkedHashMap<String,String>(), (fileName + ".als"));
        } else
            throw new ErrorSyntax("Could not import module: " + fileName);
    }

    /*
     * This function iterates through the concState hashmap and stores each
     * concurrent state name in the concStateNames list
     */
    public static void addConcStates(DashModule dashModule) {
        /* Get all the concurrent states */
        for (ConcState concState : dashModule.concStates.values()) {
            //System.out.println("Name: " + concState.name);
            System.out.println("Modified Name: " + concState.modifiedName);
            concStateNames.add(concState.name);
            concStateNamesModified.add(concState.modifiedName);
        }

        System.out.println("concStateNames size: " + concStateNames.size());
        System.out.println("concStateNamesModified size: " + concStateNamesModified.size());

        for (String name : concStateNamesModified)
            System.out.println("Modified Name: " + name);

        for (String concStateName : concStateNamesModified)
            initializeNameContainers(concStateName, dashModule);

    }

    public static void initializeNameContainers(String concStateName, DashModule dashModule) {
        List<String> names = new ArrayList<String>();
        List<Trans> transitionList = new ArrayList<Trans>();
        List<Expr> expressionList = new ArrayList<Expr>();

        for (State state : dashModule.concStates.get(concStateName).states)
            names.add(state.name);
        stateNames.put(concStateName, new ArrayList<String>(names));
        names.clear();

        for (Event event : dashModule.concStates.get(concStateName).events)
            names.add(event.name);
        eventNames.put(concStateName, new ArrayList<String>(names));
        names.clear();

        names = readVariablesDeclared(dashModule.concStates.get(concStateName).decls, names);
        declarationNames.put(concStateName, new ArrayList<String>(names));
        names.clear();

        for (Trans trans : dashModule.concStates.get(concStateName).transitions) {
            transitionList.add(trans);

            //The only kind of transition that will have declarations (decl) is a
            //transition template. Therefore, we will need to valdiate the arguments (decls)
            if (trans.transTemplate != null)
                validateTransTemplateDecl(trans.pos, concStateName, trans.transTemplate.decls);
            if (trans.doExpr != null)
                expressionList.add(trans.doExpr.expr);
            if (trans.whenExpr != null)
                expressionList.add(trans.whenExpr.expr);

        }
        expressions.put(concStateName, new ArrayList<Expr>(expressionList));
        transitions.put(concStateName, new ArrayList<Trans>(transitionList));
        expressionList.clear();
        transitionList.clear();

        addExprFromConcState(dashModule.concStates.get(concStateName));
    }

    public static void validateConcStates(DashModule dashModule) {
        for (String concStateName : concStateNamesModified) {
            ConcState currentConcState = dashModule.concStates.get(concStateName);
            currentConcStateValidated = currentConcState;

            if (!hasDefaultState(currentConcState.states))
                throw new ErrorSyntax(dashModule.concStates.get(concStateName).pos, "A default state is required.");

            hasSameStateName(concStateName, currentConcState.states);
            hasSameTransName(concStateName, currentConcState.transitions);
            hasSameEventName(concStateName, currentConcState.events);

            for (State state : currentConcState.states) {
                if (!hasDefaultState(state.states))
                    throw new ErrorSyntax(state.pos, "A default state is required.");

                hasSameStateName(concStateName, state.states);
                hasSameTransName(concStateName, state.transitions);
            }
        }
    }

    public static void addExprFromConcState(ConcState currentConcState) {
        List<Expr> localExpressions = new ArrayList<Expr>(expressions.get(currentConcState.modifiedName));

        if (currentConcState.init.size() > 0) {
            for (DashInit init : currentConcState.init)
                localExpressions.add(init.expr);
        }
        if (currentConcState.invariant.size() > 0) {
            for (DashInvariant invariant : currentConcState.invariant)
                localExpressions.add(invariant.expr);
        }
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
    }

    public static void clearContainers() {
        orStateCount = 0;
        concStateNames = new ArrayList<String>();
        concStateNamesModified = new ArrayList<String>();
        transitions = new HashMap<String,List<Trans>>();
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

