package edu.mit.csail.sdg.parser;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4.Pos;
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

public class DASHValidation {

    static int          orStateCount     = 0;

    /*
     * A list of all the transitions in the DASH model. This is used for validation
     * purposes. This is accessed by Alloy.cup when parsing a transition.
     */
    static List<Trans>  transitions      = new ArrayList<Trans>();

    /*
     * A list of all the signature names in the DASH model. This is used for
     * validation purposes. This is accessed by Alloy.cup when parsing a signature.
     */
    static List<String> sigNames         = new ArrayList<String>();

    /*
     * A list of all the func and pred names in the DASH model. This is used for
     * validation purposes. This is accessed by Alloy.cup when parsing a signature.
     */
    static List<String> funcNames        = new ArrayList<String>();

    /*
     * A list of all the concurrent state names in the DASH model. This is used for
     * validation purposes. This is accessed by Alloy.cup when parsing a transition.
     */
    static List<String> concStateNames   = new ArrayList<String>();

    /*
     * A list of all the state names in the DASH model. This is used for validation
     * purposes. This is accessed by Alloy.cup when parsing a transition.
     */
    static List<String> stateNames       = new ArrayList<String>();

    /*
     * A list of all the event names in the DASH model. This is used for validation
     * purposes. This is accessed by Alloy.cup when parsing an event.
     */
    static List<String> eventNames       = new ArrayList<String>();


    /*
     * A list of all the variable declarations in the DASH model. This is used for
     * validation purposes. This is accessed by Alloy.cup when parsing a var
     * declaration.
     */
    static List<Decl>   declarations     = new ArrayList<Decl>();
    static List<String> declarationNames = new ArrayList<String>();

    /*
     * Store the quantifier variables in this container. Example: (all c: variable
     * |...) c would be the quantifer variable in this case
     */
    static List<String> quantifierVars   = new ArrayList<String>();

    /*
     * A list of all the expressions in the DASH model. This is used for validation
     * purposes. This is accessed by Alloy.cup when parsing an expression.
     */
    static List<Expr>   expressions      = new ArrayList<Expr>();

    static List<String> keywords         = Arrays.asList("none", "no", "one", "some", "all");

    /*
     * Make sure that transitions declared are legal. An illegal transition would be
     * on that refers to an event that has not been declared, or attempts to make a
     * transition to a state that has not been declared, etc.
     */
    public static void hasLegalTransCommand(String stateName, List<Object> stateItems) {
        for (String name : stateNames)
            System.out.println("State: " + name);
        for (String name : eventNames)
            System.out.println("Event: " + name);

        for (Trans transition : transitions) {
            if (transition.onExpr != null) {
                validateTransRef(transition.onExpr, transition.onExprPos, eventNames);
            }
            if (transition.gotoExpr.size() > 0) {
                for (String gotoName : transition.gotoExpr) {
                    System.out.println("Checking :" + gotoName);
                    validateTransRef(gotoName, transition.gotoExprPos, stateNames);
                }
            }
            if (transition.fromExpr.size() > 0) {
                for (String fromName : transition.fromExpr) {
                    validateTransRef(fromName, transition.gotoExprPos, stateNames);
                }
            }
            if (transition.templateParam.size() > 0) {
                for (ExprVar arg : transition.templateParam) {
                    if (!stateNames.contains(arg.toString()) && !eventNames.contains(arg.toString()))
                        throw new ErrorSyntax(arg.pos, "Could not resolve reference to: " + arg.toString());
                }
            }
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
    public static void readVariablesDeclared() {
        /* Store the names of each variable inside declarationNames */
        for (Decl decl : declarations) {
            for (Object name : decl.names)
                declarationNames.add(name.toString());
        }
    }


    public static void validateExprVar() {
        for (Expr expr : expressions) {
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

    public static void validateTransTemplateDecl(Pos pos, List<Decl> decls) {
        for (Decl decl : decls) {
            if (decl.expr instanceof ExprVar) {
                System.out.println("Expr: " + decl.expr.toString());
                if (!decl.expr.toString().equals("State") && !decl.expr.toString().equals("Event"))
                    throw new ErrorSyntax(pos, "Expected Type: Abstract Boolean or Abstract Event or Abstract State");
            }
            if (decl.expr instanceof ExprVar && decl.expr.toString().equals("Event")) {
                System.out.println("Adding to Events: " + decl.get().toString());
                eventNames.add(decl.get().toString());
            }
            if (decl.expr instanceof ExprVar && decl.expr.toString().equals("State")) {
                System.out.println("Adding to State: " + decl.get().toString());
                stateNames.add(decl.get().toString());
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

        if (!declarationNames.contains(variable) && !keywords.contains(variable) && !quantifierVars.contains(variable) && !sigNames.contains(variable) && !funcNames.contains(variable)) {
            throw new ErrorSyntax(var.pos, "Could not resolve reference to: " + variable);
        }
    }

    /* Ensure that conc states have a default state */
    public static Boolean hasDefaultState(String stateName, List<Object> stateItems) {
        orStateCount = 0;
        //System.out.println("In state: " + stateName);

        for (Object item : stateItems) {

            if (item instanceof State) {
                State currentState = ((State) item);
                //System.out.println("Current state item: " + (currentState.name));
                orStateCount++;
            }
        }

        /*
         * There is no need to declare a default state if no states have been declared
         * inside a concurrent state
         */
        if (orStateCount == 0)
            return true;

        for (Object item : stateItems) {
            if (item instanceof State) {
                if (((State) item).isDefault)
                    return true;
            }
        }
        return false;
    }

    /* Ensure that conc states do not have orstates with the same name */
    public static Boolean hasSameStateName(String name, List<Object> stateItems) {
        String stateName = "";
        String currentStateName = "";
        Boolean sameStateFound = false;

        for (Object item : stateItems) {
            if (item instanceof State) {
                stateName = ((State) item).name;
                for (Object state : stateItems) {
                    if (state instanceof State) {
                        if (stateName.equals(((State) state).name) && sameStateFound)
                            return true;
                        if (stateName.equals(((State) state).name) && !sameStateFound)
                            sameStateFound = true;
                    }
                }
            }
            sameStateFound = false;
        }
        return false;
    }

    /* Ensure that conc states do not have orstates with the trans name */
    public static Boolean hasSameTransName(String name, List<Object> stateItems) {
        String transName = "";
        String currentTransName = "";
        Boolean sameTransFound = false;

        for (Object item : stateItems) {
            if (item instanceof Trans) {
                transName = ((Trans) item).name;
                for (Object trans : stateItems) {
                    if (trans instanceof Trans) {
                        if (transName.equals(((State) trans).name) && sameTransFound)
                            return true;
                        if (transName.equals(((State) trans).name) && !sameTransFound)
                            sameTransFound = true;
                    }
                }
            }
            sameTransFound = false;
        }
        return false;
    }

    /* Ensure that conc states do not have events with the same name */
    public static Boolean hasSameEventName(String name, List<Object> stateItems) {
        String eventName = "";
        String currentEventName = "";
        Boolean sameEventFound = false;

        for (Object item : stateItems) {
            if (item instanceof Event) {
                eventName = ((Event) item).name;
                for (Object event : stateItems) {
                    if (event instanceof Event) {
                        if (eventName.equals(((Event) event).name) && sameEventFound && !eventName.isEmpty())
                            throw new ErrorSyntax(((Event) event).pos, "This event has already been previous declared.");
                        if (eventName.equals(((Event) event).name) && !sameEventFound && !eventName.isEmpty())
                            sameEventFound = true;
                    }
                }
            }
            sameEventFound = false;
        }
        return false;
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

    public static void clearContainers() {
        orStateCount = 0;
        transitions = new ArrayList<Trans>();
        sigNames = new ArrayList<String>();
        funcNames = new ArrayList<String>();
        stateNames = new ArrayList<String>();
        eventNames = new ArrayList<String>();
        declarations = new ArrayList<Decl>();
        declarationNames = new ArrayList<String>();
        quantifierVars = new ArrayList<String>();
        expressions = new ArrayList<Expr>();
    }
}

