package ca.uwaterloo.watform.transform;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Attr.AttrType;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.CommandScope;
import ca.uwaterloo.watform.ast.DashAction;
import ca.uwaterloo.watform.ast.DashConcState;
import ca.uwaterloo.watform.ast.DashCondition;
import ca.uwaterloo.watform.ast.DashInit;
import ca.uwaterloo.watform.ast.DashInvariant;
import ca.uwaterloo.watform.ast.DashState;
import ca.uwaterloo.watform.ast.DashTrans;
import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.parser.DashOptions;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBadJoin;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprBinary.Op;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprHasName;
import edu.mit.csail.sdg.ast.ExprITE;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Sig.PrimSig;
 
public class CoreDashToAlloy {
 
    public static DashModule convertToAlloyAST(DashModule module) {	
    	createCommand(module);
    	
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
        createInvariantFact(module);
        if (DashOptions.hasEvents) createSingleStepFact(module);
        
        return module;
    }

    /* Used by other functions to help create signature ASTs */
    public static void addSigAST(DashModule module, String sigName, ExprVar isExtends, List<ExprVar> sigParent, List<Decl> decls, Pos isAbstract, Pos isLone, Pos isOne, Pos isSome, Pos isPrivate) {
        module.addSig(sigName, isExtends, sigParent, decls, null, null, AttrType.ABSTRACT.makenull(isAbstract), AttrType.LONE.makenull(isLone), AttrType.ONE.makenull(isOne), AttrType.SOME.makenull(isSome), AttrType.PRIVATE.makenull(isPrivate));
    }
    
    static void createTransitionsAST(DashModule module) {
        for (DashTrans transition : module.transitions.values()) {
            createPreConditionAST(transition, module);
            createPostConditionAST(transition, module);
            createTransCallAST(transition, module);
            createEnabledNextStepAST(transition, module);
            createSemanticsAST(transition, module);
        }
    }
    
    /* Create the single input assumption */
    static void createSingleStepFact(DashModule module)
    {
    	System.out.println("Adding in Single Step Fact.");
        // Creating the following expression: all s: Snapshot | lone (s.events & EnvironmentEvent)
    	
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        
        Expr snapshot = ExprUnary.Op.ONE.make(null, ExprVar.make(null, "Snapshot"));
        Expr s = ExprVar.make(null, "s");
        Expr expression = null; //This is the final expression to be stored in the Fact AST
        
        /* Creating the following expression: lone (s.events & EnvironmentEvent) */
        Expr rightQT = null;
        Expr join = ExprBadJoin.make(null, null, s, ExprVar.make(null, "events")); // s.events
        Expr rightBinary = ExprBinary.Op.INTERSECT.make(null, null, join, ExprVar.make(null, "EnvironmentEvent")); // s'.events & InternalEvent
        rightQT = ExprUnary.Op.LONE.make(null, rightBinary); // no (s'.events & InternalEvent)
        
        /* Creating the following expression: all s: Snapshot | lone (s.events & EnvironmentEvent) */
        a.add((ExprVar) s);
        decls.add(new Decl(null, null, null, null, a, mult(snapshot))); //s: Snapshot
        expression = ExprQt.Op.ALL.make(null, null, new ArrayList<Decl>(decls), rightQT); //all s: Snapshot | lone (s.events & EnvironmentEvent)
        
        module.addFact(null, "", expression);
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
        addSigAST(module, "Snapshot", ExprVar.make(null, "extends"), sigParent, decls, null, null, null, null, null);
    }
    
    static void createStateSpaceAST(DashModule module) {
        addSigAST(module, "SystemState", ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "StateLabel"))), new ArrayList<Decl>(), new Pos("abstract", 0, 0), null, null, null, null);

        for (DashConcState concState : module.topLevelConcStates.values()) {
        	if(module.stateHierarchy)
        		addSigAST(module, concState.modifiedName, ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "SystemState"))), new ArrayList<Decl>(), new Pos("abstract", 0, 0), null, null, null, null);
        	else if(concState.states.size() > 0)
        		addSigAST(module, concState.modifiedName, ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "SystemState"))), new ArrayList<Decl>(), new Pos("abstract", 0, 0), null, null, null, null);
        	else
        		addSigAST(module, concState.modifiedName, ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "SystemState"))), new ArrayList<Decl>(), null, null,  new Pos("one", 0, 0), null, null);
        	
            createStateAST(concState, module);
        }
    }

    static void createStateAST(DashConcState concState, DashModule module) {
        for (DashState state : concState.states) {
        	if(state.states.size() == 0)
        		addSigAST(module, state.modifiedName, ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, concState.modifiedName))), new ArrayList<Decl>(), null, null, new Pos("one", 0, 0), null, null);
        	else
        		addSigAST(module, state.modifiedName, ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, concState.modifiedName))), new ArrayList<Decl>(), new Pos("abstract", 0, 0), null, null, null, null);
        	
            for(DashState innerState: state.states) {
            	if(innerState.states.size() == 0)
            		addSigAST(module, innerState.modifiedName, ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, state.modifiedName))), new ArrayList<Decl>(), null, null, new Pos("one", 0, 0), null, null);
            	else {
            		addSigAST(module, innerState.modifiedName, ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, state.modifiedName))), new ArrayList<Decl>(), new Pos("abstract", 0, 0), null, null, null, null);
            		createChildStateAST(innerState, module);
            	}
            }
        }

        for (DashConcState innerConcState : concState.concStates) {
            addSigAST(module, innerConcState.modifiedName, ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, concState.modifiedName))), new ArrayList<Decl>(), new Pos("abstract", 0, 0), null, null, null, null);
            createStateAST(innerConcState, module);
        }
    }
    
    static void createChildStateAST(DashState state, DashModule module) {
        for(DashState innerState: state.states) {
        	if(innerState.states.size() == 0)
        		addSigAST(module, innerState.modifiedName, ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, state.modifiedName))), new ArrayList<Decl>(), null, null, new Pos("one", 0, 0), null, null);
        	else {
        		addSigAST(module, innerState.modifiedName, ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, state.modifiedName))), new ArrayList<Decl>(), new Pos("abstract", 0, 0), null, null, null, null);
        		createChildStateAST(innerState, module);
        	}
        }
    }

    static void createEventSpaceAST(DashModule module) {
        for (String key : module.events.keySet()) {
            if (module.events.get(key).type.equals("env event"))
                addSigAST(module, key, ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "EnvironmentEvent"))), new ArrayList<Decl>(), null, null, new Pos("one", 0, 0), null, null);
            if (module.events.get(key).type.equals("event"))
                addSigAST(module, key, ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "InternalEvent"))), new ArrayList<Decl>(), null, null, new Pos("one", 0, 0), null, null);
        }
    }

    static void createTransitionSpaceAST(DashModule module) {
        for (DashTrans transition : module.transitions.values()) {
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
            Expr left = null;
        	for(DashState state: module.states.values()){
        		if(state.states.size() > 0 && state.modifiedName.equals(transition.fromExpr.fromExpr.get(0).replace('/', '_'))) {
        			left = ExprVar.make(null, transition.fromExpr.fromExpr.get(0).replace('/', '_'));
        			Expr right = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "conf"));
        			binaryFrom = ExprBinary.Op.INTERSECT.make(null, null, left, mult(right));
        			binaryFrom = ExprUnary.Op.SOME.make(null, binaryFrom);
        			break;
        		}
        		else if(state.states.size() == 0 && state.modifiedName.equals(transition.fromExpr.fromExpr.get(0).replace('/', '_'))){
                    left = ExprVar.make(null, transition.fromExpr.fromExpr.get(0).replace('/', '_'));
                    Expr right = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "conf"));
                    binaryFrom = ExprBinary.Op.IN.make(null, null, left, mult(right));
        			break;
        		}     			
        	}
        	if(binaryFrom == null) {
        		Expr right = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "conf"));
        		Expr source = ExprVar.make(null, transition.fromExpr.fromExpr.get(0).replace('/', '_'));
        		binaryFrom = ExprBinary.Op.IN.make(null, null, source, mult(right));
        	}
        }

        /*
         * Creating the following expression: onExprName in (s.events &
         * EnvironmentEvent)
         */
        Expr binaryOn = null;
        if (transition.onExpr.name != null && DashOptions.isEnvEventModel && !module.stateHierarchy) {
            Expr left = ExprVar.make(null, transition.onExpr.name.replace('/', '_'));
            Expr rightJoin = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "events")); // s.events
            Expr rightBinary = ExprBinary.Op.INTERSECT.make(null, null, rightJoin, ExprVar.make(null, "EnvironmentEvent")); // s.events & EnvironmentEvent
            binaryOn = ExprBinary.Op.IN.make(null, null, left, mult(rightBinary)); //onExprName in (s.events & EnvironmentEvent)         
        }
        if (transition.onExpr.name != null && DashOptions.isEnvEventModel && module.stateHierarchy) {
        	Expr sStableTrue = ExprBinary.Op.EQUALS.make(null, null, ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "stable")), ExprVar.make(null, "True"));
            Expr left = ExprVar.make(null, transition.onExpr.name.replace('/', '_'));
            Expr rightJoin = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "events")); // s.events
            Expr rightBinary = ExprBinary.Op.INTERSECT.make(null, null, rightJoin, ExprVar.make(null, "EnvironmentEvent")); // s.events & EnvironmentEvent
            Expr ifExpr = ExprBinary.Op.IN.make(null, null, left, mult(rightBinary)); //onExprName in (s.events & EnvironmentEvent)
            Expr elseExpr = ExprBinary.Op.IN.make(null, null, left, mult(rightJoin)); //onExprName in (s.events)  
            binaryOn = ExprITE.make(null, sStableTrue, ifExpr, elseExpr);             
        }

        if (binaryOn != null)
            expression = ExprBinary.Op.AND.make(null, null, binaryFrom, binaryOn);
        else
            expression = binaryFrom;


        /* Creating the following expression: AND[whenExpr, whenExpr, ..] */
        if (transition.whenExpr != null && transition.whenExpr.exprList != null) {        	
            Expr modifiedExpr = getVarFromParentExpr(transition.whenExpr.expr, getParentConcState(transition.parentState), module);
            	
            if (expression == null)
                expression = ExprBinary.Op.AND.make(null, null, binaryFrom, modifiedExpr);
            else
                expression = ExprBinary.Op.AND.make(null, null, expression, modifiedExpr);   
        }

        return expression;
    }
    
    static Expr getPreCondForEnabled(DashTrans transition, DashModule module) {
        Expr expression = null; //This is the final expression that will be stored in the predicate AST

        Expr binaryFrom = null;
        /* Creating the following expression: sourceState in s.conf */
        if (transition.fromExpr.fromExpr.size() > 0) {       
            Expr left = null;
        	for(DashState state: module.states.values()){
        		if(state.states.size() > 0 && state.modifiedName.equals(transition.fromExpr.fromExpr.get(0).replace('/', '_'))) {
        			left = ExprVar.make(null, transition.fromExpr.fromExpr.get(0).replace('/', '_'));
        			Expr right = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "conf"));
        			binaryFrom = ExprBinary.Op.INTERSECT.make(null, null, left, mult(right));
        			binaryFrom = ExprUnary.Op.SOME.make(null, binaryFrom);
        			break;
        		}
        		else if(state.states.size() == 0 && state.modifiedName.equals(transition.fromExpr.fromExpr.get(0).replace('/', '_'))){
                    left = ExprVar.make(null, transition.fromExpr.fromExpr.get(0).replace('/', '_'));
                    Expr right = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "conf"));
                    binaryFrom = ExprBinary.Op.IN.make(null, null, left, mult(right));
        			break;
        		}     			
        	}
        	if(binaryFrom == null) {
        		Expr right = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "conf"));
        		Expr source = ExprVar.make(null, transition.fromExpr.fromExpr.get(0).replace('/', '_'));
        		binaryFrom = ExprBinary.Op.IN.make(null, null, source, mult(right));
        	}
        }

        expression = binaryFrom;

        /* Creating the following expression: AND[whenExpr, whenExpr, ..] */
        if (transition.whenExpr != null && transition.whenExpr.exprList != null) {
            for (Expr expr : transition.whenExpr.exprList) {
            	
            	Expr modifiedExpr = getVarFromParentExpr(expr, getParentConcState(transition.parentState), module);
            	
                if (expression == null)
                    expression = ExprBinary.Op.AND.make(null, null, binaryFrom, modifiedExpr);
                else
                    expression = ExprBinary.Op.AND.make(null, null, expression, modifiedExpr);
            }
        }

        return expression;
    }
    
    static String modifyExpression(Expr expr, DashTrans trans, DashModule module) {
    	String expression = expr.toString();
    	List<String> exprList = Arrays.asList(expression.split(" "));
    	String modifiedExpr = "";
    	
    	for(String oneExpr: exprList) 
    		modifiedExpr += (modifyVariable(oneExpr, trans) + ' ');
    	 	
    	return modifiedExpr;
    }
    
    static String modifyVariable(String var, DashTrans trans) {
    	DashConcState parent = getParentConcState(trans.parentState);
    	
    	while(parent != null) {
        	for(Decl decl: parent.decls) {
        		for(ExprHasName name: decl.names) {
        			if(var.equals(name.toString())) 
        				return (parent.modifiedName + "_" + name.toString());    			
        		}
        	}
        	parent = getParentConcState(parent.parent);
    	}
    	
    	return var;
    }
    

    /*
     * This function creates the AST for the precondition predicate in the Alloy
     * Model
     */
    static void createPreConditionAST(DashTrans transition, DashModule module) {
        Expr expression = null;
        expression = ExprUnary.Op.NOOP.make(null, getPreCondAST(transition, module));
        addPredicateAST(module, "pre_" + transition.modifiedName, "s", null, null, null, expression);
    }

    /*
     * This function creates the AST for the postcondition predicate in the Alloy
     * Model
     */
    static void createPostConditionAST(DashTrans transition, DashModule module) {
        Expr sStable = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "stable"));
        Expr sPrimeStable = ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), ExprVar.make(null, "stable"));
        Expr sEvents = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "events"));
        Expr sPrimeEvents = ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), ExprVar.make(null, "events"));
        ExprVar intEvent = ExprVar.make(null, "InternalEvent");
        //ExprVar extEvent = ExprVar.make(null, "ExternalEvent");
        Expr expression = null;

        //Expr binaryGoTo = null;
        /*
         * Creating the following expression: s'.conf = s.conf - sourceState +
         * destinationState
         */
        if (transition.gotoExpr.gotoExpr.size() > 0) {
            Expr gotoExpr = ExprVar.make(null, transition.gotoExpr.gotoExpr.get(0).replace('/', '_'));
            Expr fromExpr = ExprVar.make(null, transition.fromExpr.fromExpr.get(0).replace('/', '_'));
            Expr sConf = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "conf")); //s.conf
            Expr sConfPrime = ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), ExprVar.make(null, "conf"));//s'.conf
            Expr binaryRight = ExprBinary.Op.PLUS.make(null, null, ExprBinary.Op.MINUS.make(null, null, sConf, fromExpr), gotoExpr);//s.conf - fromExpr + gotoExpr
            expression = ExprBinary.Op.EQUALS.make(null, null, sConfPrime, binaryRight); //s'.conf = s.conf - fromExpr + gotoExpr
        }


        /* Creating the following expression: AND[doexpr, doexpr, ..] */
        if (transition.doExpr != null && transition.doExpr.exprList != null) {
        	
        	if (DashOptions.variablesUnchanged)
        	{
	            //These are the variables that have not been changed in the post-cond and they need to retain their values in the next snapshot
	            for (String var : getUnchangedVars(transition.doExpr.exprList, getParentConcState(transition.parentState), module, transition)) {
	                Expr binaryLeft = ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), ExprVar.make(null, var)); //s'.variableParent_varName
	                Expr binaryRight = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, var)); //s'.variableParent_varName
	                Expr binaryEquals = ExprBinary.Op.EQUALS.make(null, null, binaryLeft, binaryRight);
	                expression = ExprBinary.Op.AND.make(null, null, expression, binaryEquals);
	            }
        	}
            
            Expr modifiedExpr = getVarFromParentExpr(transition.doExpr.expr, getParentConcState(transition.parentState), module);
            expression = ExprBinary.Op.AND.make(null, null, expression, modifiedExpr);
        }

        /* Creating the following expression(s): s'.variable = s.variable */
        if (transition.doExpr == null) {
            //These are the variables that have not been changed in the post-cond and they need to retain their values in the next snapshot
            for (String var : getUnchangedVars(new ArrayList<Expr>(), getParentConcState(transition.parentState), module, transition)) {
                Expr binaryLeft = ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), ExprVar.make(null, var)); //s'.variableParent_varName
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
            Expr ifExpr = ExprBinary.Op.EQUALS.make(null, null, ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), ExprVar.make(null, "stable")), ExprVar.make(null, "True"));
            Expr ElseExpr = ExprBinary.Op.EQUALS.make(null, null, ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), ExprVar.make(null, "stable")), ExprVar.make(null, "False"));
            Expr ifCond = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "testIfNextStable"));
            ifCond = ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), ifCond);
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
            Expr sPrimeStableFalse = ExprBinary.Op.EQUALS.make(null, null, sPrimeStable, ExprVar.make(null, "False")); //s'.stable = False
            Expr sStableTrue = ExprBinary.Op.EQUALS.make(null, null, sStable, ExprVar.make(null, "True")); //s.stable = True
            Expr sPrimeEnvAndIntEvn = ExprBinary.Op.INTERSECT.make(null, null, sPrimeEvents, intEvent); //s'events & InternalEvent
            if(transition.sendExpr != null && transition.sendExpr.name != null)
            	sPrimeEnvAndIntEvn = ExprBinary.Op.MINUS.make(null, null, sPrimeEnvAndIntEvn, ExprVar.make(null, transition.sendExpr.name)); //s'events & InternalEvent - sendEvent

            Expr sEnvAndIntEvn = ExprBinary.Op.INTERSECT.make(null, null, intEvent, sEvents); //s.events & InternalEvent
            Expr noSPrimeEnvAndIntEvn = ExprUnary.Op.NO.make(null, sPrimeEnvAndIntEvn); //no (s'events & InternalEvent)

            Expr noSPrimeEnvAndIntEvnMinus = null;
            if(transition.sendExpr != null && transition.sendExpr.name != null)
            	noSPrimeEnvAndIntEvnMinus= ExprUnary.Op.NO.make(null, ExprBinary.Op.PLUS.make(null, null, sPrimeEnvAndIntEvn, sEnvAndIntEvn)); // no ((s'events & InternalEvent) - sendEvent + (s.events & InternalEvent))
            else
            	noSPrimeEnvAndIntEvnMinus= ExprUnary.Op.NO.make(null, ExprBinary.Op.MINUS.make(null, null, sPrimeEnvAndIntEvn, sEnvAndIntEvn)); // no ((s'events & InternalEvent) - (s.events & InternalEvent))

            Expr ifLowerExpr = ExprITE.make(null, sStableTrue, noSPrimeEnvAndIntEvn, noSPrimeEnvAndIntEvnMinus);

            ifLowerExpr = ExprBinary.Op.AND.make(null, null, sPrimeStableTrue, ifLowerExpr);

            Expr elseLowerExprIf = null;
            if(transition.sendExpr != null && transition.sendExpr.name != null)
            	elseLowerExprIf = ExprBinary.Op.EQUALS.make(null, null, ((ExprBinary) sPrimeEnvAndIntEvn).left, ExprVar.make(null, transition.sendExpr.name)); //s'.events & InternalEvent = {sendEvent}
            else
            	elseLowerExprIf = ExprBinary.Op.EQUALS.make(null, null, sPrimeEnvAndIntEvn, ExprVar.make(null, "none")); //s'.events & InternalEvent = {none}

            Expr sPrimeEvtAndEnv = ExprBinary.Op.INTERSECT.make(null, null, sPrimeEvents, ExprVar.make(null, "EnvironmentEvent")); //s'.events & EnvironmentEvent
            Expr sEventAndEnv = ExprBinary.Op.INTERSECT.make(null, null, sEvents, ExprVar.make(null, "EnvironmentEvent")); //s.events & EnvironmentEvent
            elseLowerExprIf = ExprBinary.Op.AND.make(null, null, elseLowerExprIf, ExprBinary.Op.EQUALS.make(null, null, sPrimeEvtAndEnv, sEventAndEnv));

            Expr elseLowerElse = null;
            if(transition.sendExpr != null && transition.sendExpr.name != null)
            	elseLowerElse = ExprBinary.Op.EQUALS.make(null, null, sPrimeEvents, ExprBinary.Op.PLUS.make(null, null, sEvents, ExprVar.make(null, transition.sendExpr.name)));
            else
            	elseLowerElse = ExprBinary.Op.EQUALS.make(null, null, sPrimeEvents, ExprBinary.Op.PLUS.make(null, null, sEvents, ExprVar.make(null, "none")));

            Expr elseLowerExpr = ExprITE.make(null, sStableTrue, elseLowerExprIf, elseLowerElse);
            elseLowerExpr = ExprBinary.Op.AND.make(null, null, sPrimeStableFalse, elseLowerExpr);

            Expr tFuncCall = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "testIfNextStable")); //s.testIfNextStable
            Expr genEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), tFuncCall); //s'.s.enabledAfterStep_transName
            Expr sPrimeGenEventT = ExprBadJoin.make(null, null, ExprVar.make(null, transition.modifiedName), genEventT); //tranName.s'.s.enabledAfterStep_transName
            Expr ssPrimeGenEventT = null;
            if(transition.sendExpr != null && transition.sendExpr.name != null)
            	ssPrimeGenEventT = ExprBadJoin.make(null, null, ExprVar.make(null, transition.sendExpr.name), sPrimeGenEventT); // sendEventName.tranName.s'.s.enabledAfterStep_transName
            else
            	ssPrimeGenEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "none"), sPrimeGenEventT); // none.tranName.s'.s.enabledAfterStep_transName


            expression = ExprBinary.Op.AND.make(null, null, expression, ExprITE.make(null, ssPrimeGenEventT, ifLowerExpr, elseLowerExpr));
        }

        /* Creating the following expression: no (s'.events & InternalEvent) */
        Expr sendExpr = null;
        if (transition.sendExpr.name == null && DashOptions.isEnvEventModel && !module.stateHierarchy) {
            Expr join = ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), ExprVar.make(null, "events")); // s'.events
            Expr rightBinary = ExprBinary.Op.INTERSECT.make(null, null, join, ExprVar.make(null, "InternalEvent")); // s'.events & InternalEvent
            sendExpr = ExprUnary.Op.NO.make(null, rightBinary); // no (s'.events & InternalEvent)
        }
        /* Creating the following expression: sentEvent in s'.events */
        if (transition.sendExpr != null && transition.sendExpr.name != null) {
            Expr join = ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), ExprVar.make(null, "events")); // s'.events
            sendExpr = ExprBinary.Op.IN.make(null, null, ExprVar.make(null, transition.sendExpr.name), mult(join)); // sentEvent in s'.events
        }

        if (sendExpr != null)
            expression = ExprBinary.Op.AND.make(null, null, expression, sendExpr);
        expression = ExprUnary.Op.NOOP.make(null, expression);

        addPredicateAST(module, "pos_" + transition.modifiedName, "s", "s_next", null, null, expression); //LOOK HERE
    }

    /*
     * This function creates the AST for the Semantics predicate in the Alloy Model
     */
    static void createSemanticsAST(DashTrans transition, DashModule module) {
        Expr expression = null;

        /* Creating the following expression: s'.taken = currentTrans */
        Expr semanticsExpr = null;
        Expr sTakenPrime = ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), ExprVar.make(null, "taken")); //s'.taken
        Expr sTaken = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "taken")); //s.taken
        if (!module.stateHierarchy) {
            semanticsExpr = ExprBinary.Op.EQUALS.make(null, null, sTakenPrime, ExprVar.make(null, transition.modifiedName)); //s'.taken = currentTrans
            expression = semanticsExpr;
        }

        List<DashTrans> innerTransitions = new ArrayList<DashTrans>();
        if(!module.stateHierarchy) {
        	if(transition.parentState instanceof DashState && ((DashState) transition.parentState).states.size() > 0){
        		for(DashState state: ((DashState) transition.parentState).states)
        			getInnerTransitions(state, innerTransitions);
        	}

        	for(DashTrans trans: innerTransitions)
        		expression = ExprBinary.Op.AND.make(null, null, expression, ExprUnary.Op.NOT.make(null, ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "pre_" + trans.modifiedName))));

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

        expression = ExprUnary.Op.NOOP.make(null, expression);
        addPredicateAST(module, "semantics_" + transition.modifiedName, "s", "s_next", null, null, expression);
    }
    
    /* Get all the transitions within a state */
    static void getInnerTransitions(DashState state, List<DashTrans> transitions) {
    	for(DashTrans trans: state.transitions) {
    		transitions.add(trans);
    	}
    	
    	for(DashState innerState: state.states) {
    		getInnerTransitions(innerState, transitions);
    	}
    }

    /*
     * This function creates the AST for the transition call (the one that refers to
     * the pre,post,semantics) predicate in the Alloy Model
     */
    static void createTransCallAST(DashTrans transition, DashModule module) {
        ExprVar s = ExprVar.make(null, "s");
        ExprVar sPrime = ExprVar.make(null, "s_next");

        Expr expression = null;

        /*
         * Creating the following expressions: post_transName[s, s'],
         * semantics_transName[s, s'], pre_transName[s]
         */
        Expr preTransCall = ExprBadJoin.make(null, null, s, ExprVar.make(null, "pre_" + transition.modifiedName)); //s.pre_transName
        
        Expr postTransCall = ExprBadJoin.make(null, null, s, ExprVar.make(null, "pos_" + transition.modifiedName)); //s.post_transName
        postTransCall = ExprBadJoin.make(null, null, sPrime, postTransCall); //s'.s.post_transName
        
        expression = ExprBinary.Op.AND.make(null, null, preTransCall, postTransCall); //AND[postTransCall, semanticsCall]

        Expr sematicsCall = ExprBadJoin.make(null, null, s, ExprVar.make(null, "semantics_" + transition.modifiedName)); //s.sematics_transName
        sematicsCall = ExprBadJoin.make(null, null, sPrime, sematicsCall); //s'.s.sematics_transName

        expression = ExprBinary.Op.AND.make(null, null, expression, sematicsCall); //AND[postTransCall, semanticsCall, preTransCall]
        addPredicateAST(module, transition.modifiedName, "s", "s_next", null, null, expression);
    }

    /*
     * This function creates an AST for the following predicate: pred
     * enabledAfterStep_transName[_s, s: Snapshot] {expressions}
     */
    static void createEnabledNextStepAST(DashTrans transition, DashModule module) {
        Expr expr = null;
        if (module.stateHierarchy) {
            expr = getPreCondForEnabled(transition, module); //Store all the pre-conditions

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
                elseExpr = ExprBinary.Op.AND.make(null, null, elseExpr, binaryIn);
            }

            expr = ExprBinary.Op.AND.make(null, null, expr, ExprITE.make(null, ifCond, ifExpr, elseExpr));
            
            addPredicateAST(module, "enabledAfterStep_" + transition.modifiedName, "_s", "s", "t", "genEvents", expr);
        }
    }

    /*
     * This function creates an AST for the following predicate: pred small_step[s,
     * s': Snapshot] { operation[s, s'] }
     */
    static void createSmallStepAST(DashModule module) {
        Expr operationCall = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "operation"));
        operationCall = ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), operationCall);

        addPredicateAST(module, "small_step", "s", "s_next", null, null, operationCall);
    }

    static void createPathAST(DashModule module) {
        List<Decl> decls = new ArrayList<Decl>();
        ExprVar s = ExprVar.make(null, "s");
        ExprVar sPrime = ExprVar.make(null, "s_next");
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
        Expr sPrime = ExprVar.make(null, "s_next");
        //Expr ssPrime = ExprBadJoin.make(null, null, s, sPrime);

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
        rightQT = ExprBinary.Op.IMPLIES.make(null, null, equalsCall, ExprBinary.Op.EQUALS.make(null, null, s, sPrime));
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
        Expr iffExpr = ExprBinary.Op.IMPLIES.make(null, null, iffLeft, iffRight); //(isEnabled[s] && no s': Snapshot | small_step[s, s']) => s.stable = False
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
        iffExpr = ExprBinary.Op.IMPLIES.make(null, null, iffLeft, iffRight);
        expr = ExprQt.Op.ALL.make(null, null, decls, iffExpr);

        if (module.stateHierarchy)
            expression = ExprBinary.Op.AND.make(null, null, expression, expr);

        expression = ExprBinary.Op.AND.make(null, null, expression, ExprVar.make(null, "path"));

        expression = ExprUnary.Op.NOOP.make(null, expression);

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
                expression = ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), expr);
            } else {
                Expr expr = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, key));
                expr = ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), expr);
                expression = ExprBinary.Op.OR.make(null, null, expression, expr);
            }
        }

        addPredicateAST(module, "operation", "s", "s_next", null, null, expression);

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
                Expr genEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), tFuncCall); //genEvents.t.enabledAfterStep_transName
                Expr sPrimeGenEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "t"), genEventT);
                Expr ssPrimeGenEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "genEvents"), sPrimeGenEventT);
                expr = ExprUnary.Op.NOT.make(null, ssPrimeGenEventT); //!enabledAfterStep_transName[s, s', t, genEvents]\n
            } else {
                Expr tFuncCall = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "enabledAfterStep_" + key)); //s.enabledAfterStep_transName
                Expr genEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), tFuncCall); //s'.s.enabledAfterStep_transName
                Expr sPrimeGenEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "t"), genEventT);
                Expr ssPrimeGenEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "genEvents"), sPrimeGenEventT);
                Expr negaged = ExprUnary.Op.NOT.make(null, ssPrimeGenEventT); //!enabledAfterStep_transName[s, s', t, genEvents]\n
                expr = ExprBinary.Op.AND.make(null, null, expr, negaged);
            }
        }

        /* No need to add this predicate if there are no transitions */
        if (module.transitions.keySet().size() > 0 && module.stateHierarchy) {
            expr = ExprUnary.Op.NOOP.make(null, expr);
            addPredicateAST(module, "testIfNextStable", "s", "s_next", "t", "genEvents", expr);
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

        //No need to add this predicate if there are no transitions in the model
        if (module.transitions.keySet().size() > 0 && module.stateHierarchy) {
            addPredicateAST(module, "isEnabled", "s", null, null, null, expr);
        }
    }

    /*
     * This function creates an AST for the following predicate: pred equals[s, s':
     * Snapshot] {}
     */
    static void createEqualsAST(DashModule module) {
        ExprVar s = ExprVar.make(null, "s");
        ExprVar sPrime = ExprVar.make(null, "s_next");
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
        addPredicateAST(module, "equals", "s", "s_next", null, null, expr);
    }

    /* This function creates the AST for the init conditions */
    static void createInitAST(DashModule module) {
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        Expr b = ExprVar.make(null, "Snapshot");
        a.add(ExprVar.make(null, "s"));
        decls.add(new Decl(null, null, null, null, a, mult(b))); //[s: Snapshot]

        ExprVar s = ExprVar.make(null, "s");
        ExprVar conf = ExprVar.make(null, "conf");
        ExprVar events = ExprVar.make(null, "events");
        ExprVar taken = ExprVar.make(null, "taken");
        ExprVar stable = ExprVar.make(null, "stable");
       
        Expr binaryLeft = ExprBadJoin.make(null, null, s, conf);
        Expr binaryRight = null;

        for (DashConcState concState : module.concStates.values()) {
            if (concState.states.size() == 0) {
            	if(concState.concStates.size() == 0) {
	                if (binaryRight == null)
	                    binaryRight = ExprVar.make(null, concState.modifiedName);
	                else
	                    binaryRight = ExprBinary.Op.PLUS.make(null, null, binaryRight, ExprVar.make(null, concState.modifiedName));
            	}
            }
            else {
                for (DashState state : concState.states) {
                	if(state.isDefault) {
	                    if (binaryRight == null)
	                        binaryRight = ExprVar.make(null, state.modifiedName);
	                    else
	                        binaryRight = ExprBinary.Op.PLUS.make(null, null, binaryRight, ExprVar.make(null, state.modifiedName));
                	}
                }
            }
        }

        Expr expression = ExprBinary.Op.EQUALS.make(null, null, binaryLeft, binaryRight);

        expression = ExprBinary.Op.AND.make(null, null, expression, ExprUnary.Op.NO.make(null, ExprBadJoin.make(null, null, s, taken))); //no s.taken
        if (DashOptions.isEnvEventModel) {
            Expr binary = ExprBinary.Op.INTERSECT.make(null, null, ExprBadJoin.make(null, null, s, events), ExprVar.make(null, "InternalEvent")); //s.events & InternalEvent
            Expr unary = ExprUnary.Op.NO.make(null, binary); //no s.events & InternalEvent
            expression = ExprBinary.Op.AND.make(null, null, expression, unary);
        }
        
        if(module.stateHierarchy) {
        	Expr sStableTrue = ExprBinary.Op.EQUALS.make(null, null, ExprBadJoin.make(null, null, s, stable), ExprVar.make(null, "True")); //s.stable = True
        	expression = ExprBinary.Op.AND.make(null, null, expression, sStableTrue);
        }
 
        for (DashInit init : module.initConditions) {
            for (Expr expr : init.exprList) {
                Expr modifiedExpr = getVarFromParentExpr(expr, init.parent, module);
                expression = ExprBinary.Op.AND.make(null, null, expression, modifiedExpr);
            }
        }

        expression = ExprUnary.Op.NOOP.make(null, expression);
        module.addFunc(null, null, "init", null, decls, null, expression);
    }

    /* Add a new predicate to the Dash Module */
    static void addPredicateAST(DashModule module, String predName, String arg1, String arg2, String arg3, String arg4, Expr expression) {
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        Expr snapshot =  ExprVar.make(null, "Snapshot");
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
            decls.add(new Decl(null, null, null, null, new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, arg3))), ExprVar.make(null, "TransitionLabel")));
            decls.add(new Decl(null, null, null, null, new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, arg4))), mult(ExprUnary.Op.SETOF.make(null, ExprVar.make(null, "InternalEvent")))));
        }

        module.addFunc(null, null, predName, null, decls, null, expression);
    }

    static void createInvariantFact(DashModule module) {
    	for(DashInvariant invar: module.invariants.values()) {
    		addInvariantFact(invar, module);
    	}
    }

    static void addInvariantFact(DashInvariant invar, DashModule module) {
    	Expr expression = null;
    	ExprVar parent = ExprVar.make(null, invar.parent.modifiedName);
    	Expr sConf = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "conf")); //s.conf
    	Expr binary = ExprBinary.Op.IN.make(null, null, parent, sConf); //parent in s.conf

    	Expr impliesExpr = null;
    	for(Expr expr: invar.exprList) {
            Expr modifiedExpr = getVarFromParentExpr(expr, getParentConcState(invar.parent), module);
        	if(impliesExpr == null)
        		impliesExpr = modifiedExpr;
        	else
        		impliesExpr = ExprBinary.Op.AND.make(null, null, impliesExpr, modifiedExpr);
        }

    	expression = ExprBinary.Op.IMPLIES.make(null, null, binary, impliesExpr);

        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        Expr snapshot =  ExprVar.make(null, "Snapshot");
        a.add(ExprVar.make(null, "s"));
        decls.add(new Decl(null, null, null, null, a, mult(snapshot)));

    	Expr quantifiedExpr = ExprQt.Op.ALL.make(null, null, decls, expression);

    	module.addFact(null, invar.name, quantifiedExpr);
    }    	
   
    public static void createCommand(DashModule module){
    	List<CommandScope> scopes = new ArrayList<CommandScope>();
    	
    	CommandScope snapshotNum = new CommandScope(null            , Sig.NONE, false,          5, 5,             1    );
    	CommandScope snapshotScope = new CommandScope(null, new PrimSig("Snapshot", AttrType.WHERE.make(new Pos(null, 0, 0))), snapshotNum.isExact, snapshotNum.startingScope, snapshotNum.endingScope, snapshotNum.increment);

    	scopes.add(snapshotScope);

        for (Sig sig : module.sigs.values()) {
        	if(sig.isAbstract == null && sig.isOne == null) {
        		CommandScope number = new CommandScope(null            , Sig.NONE, false,          3, 3,             1    );
        		CommandScope sigScope = new CommandScope(null, new PrimSig(sig.label, AttrType.WHERE.make(new Pos(null, 0, 0))), number.isExact, number.startingScope, number.endingScope, number.increment);
        		scopes.add(sigScope);
        	}
        }
        
        int eventLabelScope = 0;
        
        if(DashOptions.isEnvEventModel)
        	eventLabelScope = 3;
        
		CommandScope number = new CommandScope(null            , Sig.NONE, false,          eventLabelScope, eventLabelScope,             1    );
		CommandScope sigScope = new CommandScope(null, new PrimSig("EventLabel", AttrType.WHERE.make(new Pos(null, 0, 0))), number.isExact, number.startingScope, number.endingScope, number.increment);
		scopes.add(sigScope);
        
        c(false,ExprVar.make(null, "r"), null , ExprVar.make(null, "path") ,null, scopes, null, module);
        
        for(Command command: module.commands) {
        	System.out.println("Command: " + command.toString());
        } 
    }
    
    //Taken from the Dash.cup file for adding in commands
    private static void c(boolean follow, ExprVar o, ExprVar x, ExprVar n, Expr e, List<CommandScope> s, ExprConstant c, DashModule module) throws Err {
        int bitwidth=(-1), maxseq=(-1), overall=(-1), expects=(c==null ? -1 : c.num);
        int maxtime = (-1), mintime = (-1);
        Pos p;
		if(e != null)
        	p = o.pos.merge(n!=null ? n.span() : e.span());
        for(int i=s.size()-1; i>=0; i--) {
          Sig j=s.get(i).sig;  int k=s.get(i).startingScope;
          //p=p.merge(j.pos);
          if (j.label.equals("univ")) { overall=k; s.remove(i); continue; }
          if (j.label.equals("int"))  { if (bitwidth>=0) throw new ErrorSyntax(j.pos, "The bitwidth cannot be specified more than once."); bitwidth=k; s.remove(i); continue; }
          if (j.label.equals("seq"))  { if (maxseq>=0) throw new ErrorSyntax(j.pos, "The maximum sequence length cannot be specified more than once."); maxseq=k; s.remove(i); continue; }
          // [electrum] process time scopes
          if (j.label.equals("stepUtil")) {
              if (s.get(i).endingScope == Integer.MAX_VALUE && s.get(i).startingScope != 1) throw new ErrorSyntax(j.pos, "Unbounded time scope must start at 1.");
	      	  if (s.get(i).increment != 1) throw new ErrorSyntax(j.pos, "Step scopes must be incremented by 1.");
          	  if (k<1) throw new ErrorSyntax(j.pos, "Trace solutions must contain at least one step.");
        	  if (maxtime>=0) throw new ErrorSyntax(j.pos, "Steps scope cannot be specified more than once."); 
        	  maxtime=k; 
        	  if (s.get(i).isExact) mintime = k; 
        	  else if (s.get(i).endingScope != s.get(i).startingScope) { 
        	  	maxtime = s.get(i).endingScope; mintime = s.get(i).startingScope; }
        	  s.remove(i); continue; 
      	  }
        }
        if (n!=null)
          module.addCommand(follow, null, n, o.label.equals("c"), overall, bitwidth, maxseq, mintime, maxtime, expects, s, x);
        else
          module.addCommand(follow, null, e, o.label.equals("c"), overall, bitwidth, maxseq, mintime, maxtime, expects, s, x);
    } 

    //Take an expression in a do statement and modify any variables present. Eg: active_players should become
    //s.Game_active_players (Given that active_players is declared under the Game concurrent state)
    static Expr modifyExprWithVar(Expr expr, DashConcState parent, DashModule module) {
    	DashConcState concState = new DashConcState(parent);
    	
        Expr expression = expr; 
    	
        //If we make a reference to a conc state outside of the current conc state, find it and 
        //modify the value of the expression accordingly
    	if(expr.toString().contains("/")) {
    		String concStateRef = expr.toString().substring(0, expr.toString().indexOf("/"));
    		
    		for(DashConcState state: module.concStates.values()) {
    			if(state.name.equals(concStateRef)) {
    	            if (expr.toString().contains("'"))
    	                return ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), ExprVar.make(null, state.modifiedName + "_" + expr.toString().substring(expr.toString().indexOf("/") + 1)));
    	            else
    	            	return ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, state.modifiedName + "_" + expr.toString().substring(expr.toString().indexOf("/") + 1)));
    			}
    		}   			
    	}
    	
        final List<String> variablesInParent = module.variableNames.get(concState.modifiedName);
        final List<String> envVariablesInParent = module.envVariableNames.get(concState.modifiedName);     
        
        DashConcState outerConcState = concState.parent;

        if (variablesInParent != null)
            expression = modifyVar(expression, concState, expr, variablesInParent);
        if (envVariablesInParent != null)
            expression = modifyVar(expression, parent, expr, envVariablesInParent);

        while (outerConcState != null) {
            if (module.variableNames.get(outerConcState.modifiedName) != null)
                expression = modifyVar(expression, outerConcState, expr, module.variableNames.get(outerConcState.modifiedName));
            if (module.envVariableNames.get(concState.modifiedName) != null)
                expression = modifyVar(expression, outerConcState, expr, module.envVariableNames.get(concState.modifiedName));
            outerConcState = outerConcState.parent;
        }

        expression = replaceWithActionExpr(expression, concState, module);
        expression = replaceWithConditionExpr(expression, concState, module);
        
        return expression;
    }
    
    static Expr replaceWithActionExpr(Expr expr, DashConcState parent, DashModule module) {
        if(expr instanceof ExprVar) {
            for (DashAction value : module.actions.values()) {
                if (expr.toString().equals(value.name))
                	return getVarFromParentExpr(value.expr, parent, module);
            }
        }
        return expr;
    }
    
    static Expr replaceWithConditionExpr(Expr expr, DashConcState parent, DashModule module) {
        if(expr instanceof ExprVar) {
            for (DashCondition value : module.conditions.values()) {
                if (expr.toString().equals(value.name))
                	return getVarFromParentExpr(value.expr, parent, module);
            }
        }
        return expr;
    }
    
    static Expr modifyVar(Expr expression, DashConcState parent, Expr expr, List<String> exprList) {
        for (String var : exprList) {
            if (expr.toString().equals(var + "'"))
                return ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), ExprVar.make(null, parent.modifiedName + '_' + var));
            else if (expr.toString().equals(var)) {
                return ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, parent.modifiedName + '_' + var));
            }
        }
        return expression;
    }

    private static Expr getVarFromParentExpr(Object parentExpr, DashConcState parent, DashModule module) {
        if (parentExpr instanceof ExprBinary) {
            ExprBinary exprBinary = (ExprBinary) parentExpr;
            return getVarFromBinary(exprBinary, parent, module);
        }

        if (parentExpr instanceof ExprUnary) {
            ExprUnary unary = (ExprUnary) parentExpr;
            return getVarFromUnary(unary, parent, module);
        }
        
        if (parentExpr instanceof ExprBadJoin) {
        	return getVarFromBadJoin((ExprBadJoin) parentExpr, parent, module);
        }

        if (parentExpr instanceof ExprQt) {
            return getVarFromExprQt((ExprQt) parentExpr, parent, module);
        }

        if (parentExpr instanceof ExprVar) {
        	return modifyExprWithVar((ExprVar) parentExpr, parent, module);
        }
        
        return null;
    }

    /*
     * Breakdown a binary expression into its subcomponents Example of a binary
     * expression: #varible1 = #variable2
     */
    private static Expr getVarFromBinary(ExprBinary binary, DashConcState parent, DashModule module) {
    	Expr left = null, right = null;
        if (binary.left instanceof ExprUnary) {
            ExprUnary unary = (ExprUnary) binary.left;
            left = getVarFromUnary(unary, parent, module);
        }
        if (binary.left instanceof ExprVar) {
            left = modifyExprWithVar(binary.left, parent, module);
        }
        if (binary.left instanceof ExprBinary) {
            left = getVarFromBinary((ExprBinary) binary.left, parent, module);
        }
        if (binary.left instanceof ExprBadJoin) {
            left = getVarFromBadJoin((ExprBadJoin) binary.left, parent, module);
        }       
        if (binary.left instanceof ExprList) {
        	left = getVarFromExprList((ExprList) binary.left, parent, module);
        }
        if (binary.left instanceof ExprConstant) {
        	left = binary.left;
        }
       

        if (binary.right instanceof ExprUnary) {
            ExprUnary unary = (ExprUnary) binary.right;
            right = getVarFromUnary(unary, parent, module);
        }
        if (binary.right instanceof ExprVar) {
            right = modifyExprWithVar(binary.right, parent, module);
        }
        if (binary.right instanceof ExprBinary) {
            right = getVarFromBinary((ExprBinary) binary.right, parent, module);
        }
        if (binary.right instanceof ExprBadJoin) {
            right = getVarFromBadJoin((ExprBadJoin) binary.right, parent, module);
        }
        if (binary.right instanceof ExprList) {
        	right = getVarFromExprList((ExprList) binary.right, parent, module);
        }
        if (binary.right instanceof ExprConstant) {
        	right = binary.right;
        }
        
        return createBinaryExpr(binary.op, left, right);
    }
    
    /*
     * Breakdown a unary expression into its subcomponents Example of an unary
     * expression: one varible
     */
    private static ExprUnary getVarFromUnary(ExprUnary unary, DashConcState parent, DashModule module) {
    	Expr sub = null;
        if (unary.sub instanceof ExprVar) {
            sub = modifyExprWithVar(unary.sub, parent, module);
        }
        if (unary.sub instanceof ExprUnary) {
            sub = getVarFromUnary((ExprUnary) unary.sub, parent, module);
        }
        if (unary.sub instanceof ExprBadJoin) {
            sub = getVarFromBadJoin((ExprBadJoin) unary.sub, parent, module);
        }
        if (unary.sub instanceof ExprBinary) {
            sub = getVarFromBinary((ExprBinary) unary.sub, parent, module);
        }
        if (unary.sub instanceof ExprList) {
        	sub = getVarFromExprList((ExprList) unary.sub, parent, module);
        }
        if (unary.sub instanceof ExprConstant) {
        	sub = unary.sub;
        }
        
        return createUnaryExpr(unary.op, sub);
    }

    private static ExprBadJoin getVarFromBadJoin(ExprBadJoin joinExpr, DashConcState parent, DashModule module) {
    	Expr left = null, right = null;
        if (joinExpr.left instanceof ExprVar) {
            left = modifyExprWithVar(joinExpr.left, parent, module);
        }
        if (joinExpr.left instanceof ExprUnary) {
            left = getVarFromUnary((ExprUnary) joinExpr.left, parent, module);
        }
        if (joinExpr.left instanceof ExprBadJoin) {
            left = getVarFromBadJoin((ExprBadJoin) joinExpr.left, parent, module);
        }
        if (joinExpr.left instanceof ExprBinary) {
        	left = getVarFromBinary((ExprBinary) joinExpr.left, parent, module);
        }
        if (joinExpr.left instanceof ExprList) {
        	left = getVarFromExprList((ExprList) joinExpr.left, parent, module);
        }
        if (joinExpr.left instanceof ExprConstant) {
        	left = joinExpr.left;
        }
                
        if (joinExpr.right instanceof ExprVar) {
            right = modifyExprWithVar(joinExpr.right, parent, module);
        }
        if (joinExpr.right instanceof ExprUnary) {
            right = getVarFromUnary((ExprUnary) joinExpr.right, parent, module);
        }
        if (joinExpr.right instanceof ExprBadJoin) {
            right = getVarFromBadJoin((ExprBadJoin) joinExpr.right, parent, module);
        }
        if (joinExpr.right instanceof ExprBinary) {
        	right = getVarFromBinary((ExprBinary) joinExpr.right, parent, module);
        }
        if (joinExpr.right instanceof ExprList) {
        	right = getVarFromExprList((ExprList) joinExpr.right, parent, module);
        }
        if (joinExpr.right instanceof ExprConstant) {
        	right = joinExpr.right;
        }
        
        return (ExprBadJoin) ExprBadJoin.make(null, null, left, right);
    }

    /*
     * Breakdown a quantified expression into its subcomponents
     */
    private static Expr getVarFromExprQt(ExprQt exprQt, DashConcState parent, DashModule module) {
    	Expr subExpr = null;
    	List<Decl> decls = new ArrayList<Decl>();
    	
        for (Decl decl : exprQt.decls) {
        	List<ExprVar> a = new ArrayList<ExprVar>();
        	
        	for(ExprHasName name: decl.names)
        		a.add(ExprVar.make(null, name.toString()));    
        	Expr b = getVarFromParentExpr(decl.expr, parent, module);       	
        	decls.add(new Decl(null, null, null, null, a, mult(b)));
        }

        if (exprQt.sub instanceof ExprUnary) {
        	subExpr = getVarFromUnary((ExprUnary) exprQt.sub, parent, module);
        }
        if (exprQt.sub instanceof ExprBinary) {
        	subExpr = getVarFromBinary((ExprBinary) exprQt.sub, parent, module);
        }
        if (exprQt.sub instanceof ExprVar) {
        	subExpr = modifyExprWithVar(exprQt.sub, parent, module);
        }
        if(exprQt.sub instanceof ExprList) {
        	subExpr = getVarFromExprList((ExprList) exprQt.sub, parent, module);
        }
        if(exprQt.sub instanceof ExprBadJoin) {
        	subExpr = getVarFromBadJoin((ExprBadJoin) exprQt.sub, parent, module);
        }
        
        return createExprQt(exprQt.op, decls, subExpr);
    }
    
    /*
     * Breakdown a list of expressions into its subcomponents
     */
    private static ExprList getVarFromExprList(ExprList list, DashConcState parent, DashModule module) {
    	List<Expr> exprList = new ArrayList<Expr>();
    	for(Expr expr: list.args) {
    		if(expr instanceof ExprQt) {
    			exprList.add(getVarFromExprQt((ExprQt) expr, parent, module));
    		}
    		if(expr instanceof ExprList) {
    			exprList.add(getVarFromExprList((ExprList) expr, parent, module));
    		}
            if (expr instanceof ExprUnary) {
            	exprList.add(getVarFromUnary((ExprUnary) expr, parent, module));
            }
            if (expr instanceof ExprBinary) {
            	exprList.add(getVarFromBinary((ExprBinary) expr, parent, module));
            }
            if (expr instanceof ExprBadJoin) {
            	exprList.add(getVarFromBadJoin((ExprBadJoin) expr, parent, module));
            }
            if (expr instanceof ExprVar) {
            	exprList.add(modifyExprWithVar(expr, parent, module));
            }
            if (expr instanceof ExprConstant) {
            	exprList.add(expr);
            }
    	}
    	return createExprList(list.op, exprList);
    }

    //Retrive the concurrent state inside which "item" is located
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
 
    //Find the variables that are unchanged during a transition
    static List<String> getUnchangedVars(List<Expr> exprList, DashConcState parent, DashModule module, DashTrans trans) {
    	List<String> variables = new ArrayList<String>();
    	DashConcState concState = new DashConcState(parent);
    	
    	/* Get all the variables located in the conc state inside which the transitions is declared. It will also fetch
    	 * any variables that are located in any parents of the conc state */
    	while(concState != null) {
    		for(Decl decl: concState.decls) {
    			for(ExprHasName name: decl.names)
    				variables.add(name.toString());
    		}
    		concState = concState.parent;
    	}

        List<String> unchangedVars = new ArrayList<String>(variables);
        List<String> unchangedVarsModified = new ArrayList<String>();
        
        /* Remove any variables that have been changed by this transition. (A changed variable is one
         * that is primed) */
        for (Expr expr : exprList) {
        	for(String var: variables){
        		if(expr.toString().contains(var + "'")) {
        			unchangedVars.remove(var);
        		}
        	}
        }
        
        /* Modify the names of variables that have not been changed. */
        for(String var: unchangedVars) {
        	concState = new DashConcState(parent);
        	while(concState != null) {
        		for(Decl decl: concState.decls) {
        			for(ExprHasName name: decl.names) {
        				if(name.toString().equals(var))
        					unchangedVarsModified.add(concState.modifiedName + "_" + var);
        			}        				
        		}
        		concState = concState.parent;
        	}
        }
       
        return unchangedVarsModified;
    }
    
    static ExprBinary createBinaryExpr(ExprBinary.Op op, Expr left, Expr right) {
        if(op == Op.ARROW)
        	return (ExprBinary) ExprBinary.Op.ARROW.make(null, null, left, right);
        if(op == Op.JOIN)
        	return (ExprBinary) ExprBinary.Op.JOIN.make(null, null, left, right);
        if(op == Op.DOMAIN)
        	return (ExprBinary) ExprBinary.Op.DOMAIN.make(null, null, left, right);
        if(op == Op.RANGE)
        	return (ExprBinary) ExprBinary.Op.RANGE.make(null, null, left, right);
        if(op == Op.INTERSECT)
        	return (ExprBinary) ExprBinary.Op.INTERSECT.make(null, null, left, right);
        if(op == Op.PLUSPLUS)
        	return (ExprBinary) ExprBinary.Op.PLUSPLUS.make(null, null, left, right);
        if(op == Op.PLUSPLUS)
        	return (ExprBinary) ExprBinary.Op.PLUSPLUS.make(null, null, left, right);
        if(op == Op.PLUS)
        	return (ExprBinary) ExprBinary.Op.PLUS.make(null, null, left, right);
        if(op == Op.MINUS)
        	return (ExprBinary) ExprBinary.Op.MINUS.make(null, null, left, right);
        if(op == Op.MUL)
        	return (ExprBinary) ExprBinary.Op.MUL.make(null, null, left, right);
        if(op == Op.DIV)
        	return (ExprBinary) ExprBinary.Op.DIV.make(null, null, left, right);
        if(op == Op.REM)
        	return (ExprBinary) ExprBinary.Op.REM.make(null, null, left, right);
        if(op == Op.EQUALS)
        	return (ExprBinary) ExprBinary.Op.EQUALS.make(null, null, left, right);
        if(op == Op.NOT_EQUALS)
        	return (ExprBinary) ExprBinary.Op.NOT_EQUALS.make(null, null, left, right);
        if(op == Op.IMPLIES)
        	return (ExprBinary) ExprBinary.Op.IMPLIES.make(null, null, left, right);
        if(op == Op.LT)
        	return (ExprBinary) ExprBinary.Op.LT.make(null, null, left, right);
        if(op == Op.LTE)
        	return (ExprBinary) ExprBinary.Op.LTE.make(null, null, left, right);
        if(op == Op.GT)
        	return (ExprBinary) ExprBinary.Op.GT.make(null, null, left, right);
        if(op == Op.GTE)
        	return (ExprBinary) ExprBinary.Op.GTE.make(null, null, left, right);
        if(op == Op.NOT_LT)
        	return (ExprBinary) ExprBinary.Op.NOT_LT.make(null, null, left, right);
        if(op == Op.NOT_LTE)
        	return (ExprBinary) ExprBinary.Op.NOT_LTE.make(null, null, left, right);
        if(op == Op.NOT_GT)
        	return (ExprBinary) ExprBinary.Op.NOT_GT.make(null, null, left, right);
        if(op == Op.NOT_GTE)
        	return (ExprBinary) ExprBinary.Op.NOT_GTE.make(null, null, left, right);
        if(op == Op.SHL)
        	return (ExprBinary) ExprBinary.Op.SHL.make(null, null, left, right);
        if(op == Op.SHA)
        	return (ExprBinary) ExprBinary.Op.SHA.make(null, null, left, right);
        if(op == Op.SHR)
        	return (ExprBinary) ExprBinary.Op.SHR.make(null, null, left, right);
        if(op == Op.IN)
        	return (ExprBinary) ExprBinary.Op.IN.make(null, null, left, right);
        if(op == Op.NOT_IN)
        	return (ExprBinary) ExprBinary.Op.NOT_IN.make(null, null, left, right);
        if(op == Op.AND)
        	return (ExprBinary) ExprBinary.Op.AND.make(null, null, left, right);
        if(op == Op.OR)
        	return (ExprBinary) ExprBinary.Op.OR.make(null, null, left, right);
        if(op == Op.IFF)
        	return (ExprBinary) ExprBinary.Op.IFF.make(null, null, left, right);
        if(op == Op.UNTIL)
        	return (ExprBinary) ExprBinary.Op.UNTIL.make(null, null, left, right);
        if(op == Op.RELEASES)
        	return (ExprBinary) ExprBinary.Op.RELEASES.make(null, null, left, right);
        if(op == Op.SINCE)
        	return (ExprBinary) ExprBinary.Op.SINCE.make(null, null, left, right);
        if(op == Op.TRIGGERED)
        	return (ExprBinary) ExprBinary.Op.TRIGGERED.make(null, null, left, right);
        
        return null;
    }
    
    static ExprUnary createUnaryExpr(ExprUnary.Op op, Expr sub) {
        if(op == ExprUnary.Op.SOMEOF)
        	return (ExprUnary) ExprUnary.Op.SOMEOF.make(null, sub);
        if(op == ExprUnary.Op.LONEOF)
        	return (ExprUnary) ExprUnary.Op.LONEOF.make(null, sub);
        if(op == ExprUnary.Op.ONEOF)
        	return (ExprUnary) ExprUnary.Op.ONEOF.make(null, sub);
        if(op == ExprUnary.Op.SETOF)
        	return (ExprUnary) ExprUnary.Op.SETOF.make(null, sub);
        if(op == ExprUnary.Op.EXACTLYOF)
        	return (ExprUnary) ExprUnary.Op.EXACTLYOF.make(null, sub);
        if(op == ExprUnary.Op.NOT)
        	return (ExprUnary) ExprUnary.Op.NOT.make(null, sub);
        if(op == ExprUnary.Op.NO)
        	return (ExprUnary) ExprUnary.Op.NO.make(null, sub);
        if(op == ExprUnary.Op.SOME)
        	return (ExprUnary) ExprUnary.Op.SOME.make(null, sub);
        if(op == ExprUnary.Op.LONE)
        	return (ExprUnary) ExprUnary.Op.LONE.make(null, sub);
        if(op == ExprUnary.Op.ONE)
        	return (ExprUnary) ExprUnary.Op.ONE.make(null, sub);
        if(op == ExprUnary.Op.TRANSPOSE)
        	return (ExprUnary) ExprUnary.Op.TRANSPOSE.make(null, sub);
        if(op == ExprUnary.Op.PRIME)
        	return (ExprUnary) ExprUnary.Op.PRIME.make(null, sub);
        if(op == ExprUnary.Op.RCLOSURE)
        	return (ExprUnary) ExprUnary.Op.RCLOSURE.make(null, sub);
        if(op == ExprUnary.Op.CLOSURE)
        	return (ExprUnary) ExprUnary.Op.CLOSURE.make(null, sub);
        if(op == ExprUnary.Op.CARDINALITY)
        	return (ExprUnary) ExprUnary.Op.CARDINALITY.make(null, sub);
        if(op == ExprUnary.Op.CAST2INT)
        	return (ExprUnary) ExprUnary.Op.CAST2INT.make(null, sub);
        if(op == ExprUnary.Op.CAST2SIGINT)
        	return (ExprUnary) ExprUnary.Op.CAST2SIGINT.make(null, sub);
        if(op == ExprUnary.Op.NOOP)
        	return (ExprUnary) ExprUnary.Op.NOOP.make(null, sub);
     
        return null;
    }
    
    static ExprList createExprList(ExprList.Op op, List<Expr> args) {
        if(op == ExprList.Op.DISJOINT)
        	return (ExprList) ExprList.make(null, null, ExprList.Op.DISJOINT, args);
        if(op == ExprList.Op.TOTALORDER)
        	return (ExprList) ExprList.make(null, null, ExprList.Op.TOTALORDER, args);
        if(op == ExprList.Op.AND)
        	return (ExprList) ExprList.make(null, null, ExprList.Op.AND, args);
        if(op == ExprList.Op.OR)
        	return (ExprList) ExprList.make(null, null, ExprList.Op.OR, args);
   
        return null;
    }
    
    static ExprQt createExprQt(ExprQt.Op op, List<Decl> decls, Expr expr) {
        if(op == ExprQt.Op.ALL)
        	return (ExprQt) ExprQt.Op.ALL.make(null, null, decls, expr);
        if(op == ExprQt.Op.NO)
        	return (ExprQt) ExprQt.Op.NO.make(null, null, decls, expr);
        if(op == ExprQt.Op.LONE)
        	return (ExprQt) ExprQt.Op.LONE.make(null, null, decls, expr);
        if(op == ExprQt.Op.ONE)
        	return (ExprQt) ExprQt.Op.ONE.make(null, null, decls, expr);
        if(op == ExprQt.Op.SOME)
        	return (ExprQt) ExprQt.Op.SOME.make(null, null, decls, expr);
        if(op == ExprQt.Op.SUM)
        	return (ExprQt) ExprQt.Op.SUM.make(null, null, decls, expr);
        if(op == ExprQt.Op.COMPREHENSION)
        	return (ExprQt) ExprQt.Op.COMPREHENSION.make(null, null, decls, expr);
   
        return null;
    }
}
