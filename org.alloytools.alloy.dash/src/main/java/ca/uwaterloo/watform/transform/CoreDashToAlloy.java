package ca.uwaterloo.watform.transform;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4.Version;
import edu.mit.csail.sdg.ast.Attr.AttrType;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.CommandScope;
import ca.uwaterloo.watform.ast.DashAction;
import ca.uwaterloo.watform.ast.DashConcState;
import ca.uwaterloo.watform.ast.DashCondition;
import ca.uwaterloo.watform.ast.DashEnter;
import ca.uwaterloo.watform.ast.DashEvent;
import ca.uwaterloo.watform.ast.DashExit;
import ca.uwaterloo.watform.ast.DashInit;
import ca.uwaterloo.watform.ast.DashInvariant;
import ca.uwaterloo.watform.ast.DashState;
import ca.uwaterloo.watform.ast.DashTrans;
import ca.uwaterloo.watform.parser.DashChangedVars;
import ca.uwaterloo.watform.parser.DashHelper;
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
	static boolean isCreatingEnabledAfterPred = false;
	static boolean isCreatingPreCond = false;
	static boolean isCreatingInit = false;
	static boolean isCreatingInvariant = false;
	static boolean isCreatingExprQt = false;
	
	static Map<String, DashChangedVars> changedExprQtVars = new LinkedHashMap<String, DashChangedVars>(); // Variables referenced using a quantifier [i.e. all p | ProcessID | Process[p]/var' = expr]
	static Map<String, DashChangedVars> changedVarByReference = new LinkedHashMap<String, DashChangedVars>();
	static List<Decl> exprQtDecls = new ArrayList<Decl>(); // All the Decls in an ExprQt (including nested ExprQts)
	
	// Keep a track of when a variable has been changed during a transition
	static Map<String, DashConcState> changedVars = new LinkedHashMap<String, DashConcState>();
	static Map<String, DashConcState> changedQuantifiedVars = new LinkedHashMap<String, DashConcState>();
	static Map<String, DashConcState> changedBinaryVars = new LinkedHashMap<String, DashConcState>();
	static Map<String, DashConcState> changedUnaryVars = new LinkedHashMap<String, DashConcState>();
	static boolean legalConstraint = false;
	static boolean changingVar = false;
	static boolean refParamChanged = false;
	
	// Keep a track of the type of expression being modified
	static List<String> modifyingExprQT = new ArrayList<String>();
	static boolean modifyingExprBinary = false;
	static boolean modifyingExprUnary = false;
	static List<Decl> quantifiedExprDecls = new ArrayList<Decl>(); // Keep a track of the decls in the current quantified expression being chekced i.e all i: sig1, j: sig2 | ... where (i: sig1 and j: sig2 are the Decls)
	
	// Keep a track of a parameterized variable being changed
	static public Map<String, Expr> paramVarRef = new LinkedHashMap <String, Expr>(); // References made to parameterized variables outside of their concurrent state  (that does not use any quantification)
	static public Map<String, Expr> paramVarRefQt = new LinkedHashMap <String, Expr>(); // References made to parameterized variables outside of their concurrent state in a quantified expression (that does not use any quantification)
	
	static Map<String, Expr> paramBuffer = new LinkedHashMap<String, Expr>();
	static Map<String, Expr> paramBufferChanged = new LinkedHashMap<String, Expr>();
	static Map<String, Expr> localBufferChanged = new LinkedHashMap<String, Expr>();
	
	// Buffer Helpers
	static List<String> bufferCommands = Arrays.asList(new String[]{"add", "remove", "removeFirst"});
	static List<String> bufferFuncCommands = Arrays.asList(new String[]{"firstElem"});
	
	// Changed parameterized buffers that are universally quantified (No need to keep this unchanged for other replicated processes since it is universally quantified for all elements in a set of Processes
	static Map<String, Expr> universalQuantBuffers = new LinkedHashMap<String, Expr>();
	static boolean foundBuffer = false;

    public static DashModule convertToAlloyAST(DashModule module) {	
    	convertCommand(module);
    	//createElectrumVars(module);
    	createrBufIdxSig(module);
    	createParamSigAST(module);
        createSnapshotSigAST(module);
        if ((!DashOptions.ctlModelChecking && !DashOptions.generateTraces) && DashOptions.generateSigAxioms) {
        	createReachabilityFact(module);
        }

        createStateSpaceAST(module);
        createEventSpaceAST(module);
        createTransitionSpaceAST(module);
        
        createStableAST(module);
        createTransitionsAST(module);
        
        createInitAST(module);
        createTestIfStableAST(module);
        createSmallStepAST(module);
        createEqualsAST(module);
        createDifferentAtomsFact(module);
        createParamConstFactAST(module);
        if(DashOptions.generateTraces) {
        	createTracesFact(module);
        }
        else if (!DashOptions.generateTraces && module.stateHierarchy) {
        	createBigStepFact(module);
        }

        createIsEnabledAST(module);
        createPathAST(module);
        if (DashOptions.generateSigAxioms) {
        	createSignificanceAxiomAST(module);
        	createOperationsAxiomAST(module);
        }
        if (DashOptions.ctlModelChecking) {
        	createCTLFact(module);
        }
        createInvariantFact(module);
        
        if (DashOptions.hasEvents && DashOptions.assumeSingleInput) {
        	createSingleStepFact(module);
        }

        DashOptions.isEnvEventModel = false;
        return module;
    }
    
    /**************************** CREATE ELECTRUM *****************************/
    
    private static void createElectrumVars(DashModule module) {
    	List<Pos> sigParams = new ArrayList<Pos>(6); sigParams.add(null); sigParams.add(null); sigParams.add(null); sigParams.add(null); sigParams.add(null); sigParams.add(new Pos("", 0, 0));
    	
    	List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        
        for (String variableName : module.variable2Expression.keySet()) {
            Expr b = module.variable2Expression.get(variableName);
            //System.out.println("Sig: " + variableName + " Expr: " + b);
            b = DashHelper.createParameterizedSnapshotVar(variableName, b, module);
            a.add(ExprVar.make(null, variableName));
            decls.add(new Decl(null, null, null, null, a, convertToExprUnary(b)));
        	
        	module.addSig(variableName, null, null, new ArrayList<Decl>(decls), null, null, AttrType.ABSTRACT.makenull(null), AttrType.LONE.makenull(null), AttrType.ONE.makenull(null), 
        			AttrType.SOME.makenull(null), AttrType.PRIVATE.makenull(null), AttrType.VARIABLE.makenull(new Pos("vars", 0 ,0)));
        	
        	a.clear();
        	decls.clear();
        }
    }
  
    /**************************** CREATING ALL SIGNATURES *****************************/
    
    private static void createrBufIdxSig (DashModule module) {
    	for (String bufIdx: module.bufferNameToIndex.values()) {
    		addSigAST(module, bufIdx, null, null, null, null, null, null, null, null);
    	}
    }

    private static void createParamSigAST(DashModule module) {
    	List<String> states = new ArrayList<String>();
    	List<String> transitions = new ArrayList<String>();
        for (DashConcState concState: module.concStates.values()) {
        	if (concState.isParameterized) {
        		states.addAll(getStates(concState));
        		transitions.addAll(getTransitions(module,concState));
        		addParamSigAST(module, concState.param, states, transitions, concState.events);
        	}
        }
    }
    
    private static void addParamSigAST(DashModule module, String name, List<String> states, List<String> transitions, List<DashEvent> events) {
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();

        for (String state : states) {
            Expr b = ExprUnary.Op.ONE.make(null, ExprVar.make(null, state));
            a.add(ExprVar.make(null, DashHelper.toLowerCase(state)));
            decls.add(new Decl(null, null, null, null, a, mult(b)));
            a.clear();
        }
        
        for (String trans : transitions) {
            Expr b = ExprUnary.Op.ONE.make(null, ExprVar.make(null, trans));
            a.add(ExprVar.make(null, DashHelper.toLowerCase(trans)));
            decls.add(new Decl(null, null, null, null, a, mult(b)));
            a.clear();
        }
        
        for (DashEvent event : events) {
            Expr b = ExprUnary.Op.ONE.make(null, ExprVar.make(null, event.modifiedName));
            a.add(ExprVar.make(null, DashHelper.toLowerCase(event.modifiedName)));
            decls.add(new Decl(null, null, null, null, a, mult(b)));
            a.clear();
        }
        
        addSigAST(module, name, null, null, decls, null, null, null, null, null);
    }

    /* Used by other functions to help create signature ASTs */
    public static void addSigAST(DashModule module, String sigName, ExprVar isExtends, List<ExprVar> sigParent, List<Decl> decls, Pos isAbstract, Pos isLone, Pos isOne, Pos isSome, Pos isPrivate) {
        module.addSig(sigName, isExtends, sigParent, decls, null, null, AttrType.ABSTRACT.makenull(isAbstract), AttrType.LONE.makenull(isLone), AttrType.ONE.makenull(isOne), AttrType.SOME.makenull(isSome), AttrType.PRIVATE.makenull(isPrivate));
    }
    
    /****************************************** CREATE TRANSITIONS (PRE, POST, SEMANTICS, ENABLEDAFTERSTEP) ***************************************/
    
    private static void createTransitionsAST(DashModule module) {
        for (DashTrans transition : module.transitions.values()) {
            createPreConditionAST(transition, module);
            createPostConditionAST(transition, module);
            createTransCallAST(transition, module);
            createEnabledNextStepAST(transition, module);
            createSemanticsAST(transition, module);
        }
    }
    
    /****************************************** SNAPSHOT SIGNATURE ***************************************/

    /*
     * This function creates the AST for the Snapshot signature in the Alloy model
     */
    private static void createSnapshotSigAST(DashModule module) {
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        
        Expr b = ExprUnary.Op.SETOF.make(null, ExprVar.make(null, "StateLabel"));
        a.add(ExprVar.make(null, "conf"));
        decls.add(new Decl(null, null, null, null, a, mult(b)));
        a.clear();

        b = ExprUnary.Op.SETOF.make(null, ExprVar.make(null, "TransitionLabel"));
        a.add(ExprVar.make(null, "taken"));
        decls.add(new Decl(null, null, null, null, a, mult(b)));
        a.clear();

        //Create AST for variable declaration:
        //stable: one Bool
        if (module.stateHierarchy) {
            b = ExprUnary.Op.ONE.make(null, ExprVar.make(null, "Bool"));
            a.add(ExprVar.make(null, "stable"));
            decls.add(new Decl(null, null, null, null, a, mult(b)));
            a.clear();
        }

        if (DashOptions.isEnvEventModel) {
            b = ExprUnary.Op.SETOF.make(null, ExprVar.make(null, "EventLabel"));
            a.add(ExprVar.make(null, "events"));
            decls.add(new Decl(null, null, null, null, a, mult(b)));//events: set Label
            a.clear();
        }
        
        if ((!DashOptions.ctlModelChecking && !DashOptions.generateTraces) && DashOptions.generateSigAxioms) {
            b = ExprBinary.Op.ARROW.make(null, null, ExprVar.make(null, "Snapshot"), ExprVar.make(null, "Snapshot"));
            a.add(ExprVar.make(null, "next_step"));
            decls.add(new Decl(null, null, null, null, a, mult(b))); //next_step: Snapshot -> Snapshot
            a.clear();
        }

        /* Creating the following expression: evnVar: mappings */
        for (String variableName : module.envVariable2Expression.keySet()) {
            b = module.envVariable2Expression.get(variableName);
            a.add(ExprVar.make(null, variableName));
            decls.add(new Decl(null, null, null, null, a, b));
            a.clear();
        }
 
        /* Creating the following expression: variable: mappings (variable: param -> mapping if parameterized)*/
        for (String variableName : module.variable2Expression.keySet()) {
            b = module.variable2Expression.get(variableName);
            b = DashHelper.createParameterizedSnapshotVar(variableName, b, module);
            a.add(ExprVar.make(null, variableName));
            decls.add(new Decl(null, null, null, null, a, convertToExprUnary(b)));
            a.clear();
        }
        
        addSigAST(module, "Snapshot", null, null, decls, null, null, null, null, null);
    }
    
    /****************************************** STATE SPACE ***************************************/
    
    /* Create the following expression: 
	       abstract sig SystemState extends StateLabel {}
		   abstract sig System extends SystemState {}
		   one sig State_Name extends System {}
		   ...
     */
    private static void createStateSpaceAST(DashModule module) {
    	addSigAST(module, "StateLabel", null, null, new ArrayList<Decl>(), new Pos("abstract", 0, 0), null, null, null, null);
        addSigAST(module, "SystemState", ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "StateLabel"))), new ArrayList<Decl>(), new Pos("abstract", 0, 0), null, null, null, null);

        for (DashConcState concState : module.topLevelConcStates.values()) {
        	if(concState.concStates.size() > 0)
        		addSigAST(module, concState.modifiedName, ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "SystemState"))), new ArrayList<Decl>(), new Pos("abstract", 0, 0), null, null, null, null);
        	else if(concState.states.size() > 0)
        		addSigAST(module, concState.modifiedName, ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "SystemState"))), new ArrayList<Decl>(), new Pos("abstract", 0, 0), null, null, null, null);
        	else
        		if (!concState.isParameterized)
        			addSigAST(module, concState.modifiedName, ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "SystemState"))), new ArrayList<Decl>(), null, null,  new Pos("one", 0, 0), null, null);
        		else
        			addSigAST(module, concState.modifiedName, ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "SystemState"))), new ArrayList<Decl>(), null, null,  null, null, null);
        	
            createStateAST(concState, module);
        }
    }

    private static void createStateAST(DashConcState concState, DashModule module) {
        for (DashState state : concState.states) {
        	if(state.states.size() == 0)
        		if (!concState.isParameterized)
        			addSigAST(module, state.modifiedName, ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, concState.modifiedName))), new ArrayList<Decl>(), null, null, new Pos("one", 0, 0), null, null);
        		else
        			addSigAST(module, state.modifiedName, ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, concState.modifiedName))), new ArrayList<Decl>(), null, null, null, null, null);
        	else
        		addSigAST(module, state.modifiedName, ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, concState.modifiedName))), new ArrayList<Decl>(), new Pos("abstract", 0, 0), null, null, null, null);
        	
            for(DashState innerState: state.states) {
            	if(innerState.states.size() == 0)
            		if (!concState.isParameterized)
            			addSigAST(module, innerState.modifiedName, ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, state.modifiedName))), new ArrayList<Decl>(), null, null, new Pos("one", 0, 0), null, null);
            		else
            			addSigAST(module, innerState.modifiedName, ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, state.modifiedName))), new ArrayList<Decl>(), null, null, null, null, null);
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
    
    private static void createChildStateAST(DashState state, DashModule module) {
        for(DashState innerState: state.states) {
        	if(innerState.states.size() == 0)
        		addSigAST(module, innerState.modifiedName, ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, state.modifiedName))), new ArrayList<Decl>(), null, null, new Pos("one", 0, 0), null, null);
        	else {
        		addSigAST(module, innerState.modifiedName, ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, state.modifiedName))), new ArrayList<Decl>(), new Pos("abstract", 0, 0), null, null, null, null);
        		createChildStateAST(innerState, module);
        	}
        }
    }
    
    /****************************************** EVENT SPACE ***************************************/

    private static void createEventSpaceAST(DashModule module) {
    	addSigAST(module, "EventLabel", null, null, new ArrayList<Decl>(), new Pos("abstract", 0, 0), null, null, null, null);
        addSigAST(module, "EnvironmentEvent", ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "EventLabel"))), new ArrayList<Decl>(), new Pos("abstract", 0, 0), null, null, null, null);
        addSigAST(module, "InternalEvent", ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "EventLabel"))), new ArrayList<Decl>(), new Pos("abstract", 0, 0), null, null, null, null);
    	
        for (String key : module.events.keySet()) {
            if (module.events.get(key).type.equals("env event"))
            	if (!module.events.get(key).parent.isParameterized)
            		addSigAST(module, key, ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "EnvironmentEvent"))), new ArrayList<Decl>(), null, null, new Pos("one", 0, 0), null, null);
            	else
            		addSigAST(module, key, ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "EnvironmentEvent"))), new ArrayList<Decl>(), null, null, null, null, null);
            if (module.events.get(key).type.equals("event"))
            	if (!module.events.get(key).parent.isParameterized)
            		addSigAST(module, key, ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "InternalEvent"))), new ArrayList<Decl>(), null, null, new Pos("one", 0, 0), null, null);
            	else
            		addSigAST(module, key, ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "InternalEvent"))), new ArrayList<Decl>(), null, null, null, null, null);
        }
    }
    
    /****************************************** TRANSITION SPACE ***************************************/


    private static void createTransitionSpaceAST(DashModule module) {
    	addSigAST(module, "TransitionLabel", null, null, new ArrayList<Decl>(), new Pos("abstract", 0, 0), null, null, null, null);
        for (DashTrans transition : module.transitions.values()) {
        	if (transition.parentConcState.isParameterized)
        		addSigAST(module, transition.modifiedName, ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "TransitionLabel"))), new ArrayList<Decl>(), null, null, null, null, null);
        	else  
        		addSigAST(module, transition.modifiedName, ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "TransitionLabel"))), new ArrayList<Decl>(), null, null, new Pos("one", 0, 0), null, null);
        }
    }
    
    /****************************************** PRE CONIDTION PREDICATE ***************************************/

    
    /*
     * This function creates the AST for the precondition predicate in the Alloy
     * Model
     */
    private static void createPreConditionAST(DashTrans transition, DashModule module) {
        Expr expression = null;
        expression = ExprUnary.Op.NOOP.make(null, getPreCondAST(transition, module));
        if (transition.parentConcState.isParameterized)
        	addParameterizedPredicateAST(module, "pre_" + transition.modifiedName, "s", null, null, null, transition.parentConcState.param, expression);
        else
        	addPredicateAST(module, "pre_" + transition.modifiedName, "s", null, null, null, expression);
    }

    /*
     * Create the pre-conditions AST and returns it. Is used both for creating the
     * pre-cond predicate and for adding pre-conditions to the
     * enabledAfterStep_transName predicate
     */
    private static Expr getPreCondAST(DashTrans transition, DashModule module) {
        Expr expression = null; //This is the final expression that will be stored in the predicate AST
        isCreatingPreCond = true;
        Expr binaryFrom = null;
        /* Creating the following expression: sourceState in s.conf */
        if (transition.fromExpr.fromExpr.size() > 0) {       
            Expr left = null;
        	for(DashState state: module.states.values()){
        		if(state.states.size() > 0 && state.modifiedName.equals(transition.fromExpr.fromExpr.get(0).replace('/', '_'))) {
        			if(transition.parentConcState.isParameterized) {
        				String fromState = transition.fromExpr.fromExpr.get(0).replace('/', '_');
        				left = ExprVar.make(null, DashHelper.toLowerCase(fromState));
        				left = ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "p"), left);
        			}
        			else {
        				left = ExprVar.make(null, transition.fromExpr.fromExpr.get(0).replace('/', '_'));
        			}
        			Expr right = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "conf"));
        			binaryFrom = ExprBinary.Op.INTERSECT.make(null, null, left, mult(right));
        			binaryFrom = ExprUnary.Op.SOME.make(null, binaryFrom);       				
        			break;
        		}
        		else if(state.states.size() == 0 && state.modifiedName.equals(transition.fromExpr.fromExpr.get(0).replace('/', '_'))){
        			if(transition.parentConcState.isParameterized) {
        				String fromState = transition.fromExpr.fromExpr.get(0).replace('/', '_');
        				left = ExprVar.make(null, DashHelper.toLowerCase(fromState));
        				left = ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "p"), left);
        			}
        			else {
        				left = ExprVar.make(null, transition.fromExpr.fromExpr.get(0).replace('/', '_'));
        			}
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
        
        String onCommand = transition.onExpr == null ? "" : transition.onExpr.name.replace('/', '_');
        if (transition.onExpr != null && transition.onExpr.name != null && DashOptions.isEnvEventModel && !module.stateHierarchy) {
        	Expr left = transition.onExpr.parent.isParameterized ? ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "p"), ExprVar.make(null, DashHelper.toLowerCase(onCommand))) : ExprVar.make(null, onCommand);
            Expr rightJoin = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "events")); // s.events
            Expr rightBinary = ExprBinary.Op.INTERSECT.make(null, null, rightJoin, ExprVar.make(null, "EnvironmentEvent")); // s.events & EnvironmentEvent
            binaryOn = ExprBinary.Op.IN.make(null, null, left, mult(rightBinary)); //onExprName in (s.events & EnvironmentEvent)         
        }
        
        if (transition.onExpr != null && transition.onExpr.name != null && transition.onExpr.isInternal && DashOptions.isEnvEventModel && module.stateHierarchy) {
        	Expr sStableTrue = ExprBinary.Op.EQUALS.make(null, null, ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "stable")), ExprVar.make(null, "True")); //s.stable = True
        	Expr notSStableTrue = ExprUnary.Op.NOT.make(null, sStableTrue); // !(s.stable = True)
            Expr left = transition.onExpr.parent.isParameterized ? ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "p"), ExprVar.make(null, DashHelper.toLowerCase(onCommand))) : ExprVar.make(null, onCommand);
            Expr rightJoin = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "events")); // s.events
            Expr eventInSEvents = ExprBinary.Op.IN.make(null, null, left, mult(rightJoin)); //onExprName in (s.events)  
            binaryOn = ExprBinary.Op.OR.make(null, null, notSStableTrue, eventInSEvents); // !(s.stable = True) or onExprName in (s.events)          
        }
        else if (transition.onExpr != null && transition.onExpr.name != null && DashOptions.isEnvEventModel && module.stateHierarchy) {
        	Expr sStableTrue = ExprBinary.Op.EQUALS.make(null, null, ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "stable")), ExprVar.make(null, "True"));
        	Expr left = transition.onExpr.parent.isParameterized ? ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "p"), ExprVar.make(null, DashHelper.toLowerCase(onCommand))) : ExprVar.make(null, onCommand);
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

        isCreatingPreCond = false;
        return expression;
    }
    
    private static Expr getPreCondForEnabled(DashTrans transition, DashModule module) {
        Expr expression = null; //This is the final expression that will be stored in the predicate AST

        Expr binaryFrom = null;
        /* Creating the following expression: sourceState in s.conf (if no inner OR states)
         * else create: some sourceState in s.conf */
        if (transition.fromExpr.fromExpr.size() > 0) {       
            Expr left = null;
            
        	DashState sourceState = DashToCoreDash.getStateFromName(transition.fromExpr.fromExpr.get(0), module);
        	String fromExprStr = transition.fromExpr.fromExpr.get(0).replace('/', '_');
        	if (transition.parentConcState.isParameterized)
        		fromExprStr = DashHelper.toLowerCase(fromExprStr);
        	
        	if(sourceState != null && sourceState.states.size() > 0) {
        		left = ExprVar.make(null, fromExprStr);
        		if (transition.parentConcState.isParameterized) left = ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "p"), left);
        		Expr right = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "conf"));
        		binaryFrom = ExprBinary.Op.INTERSECT.make(null, null, left, mult(right));
        		binaryFrom = ExprUnary.Op.SOME.make(null, binaryFrom);
        	}
        	else if(sourceState != null && sourceState.states.size() == 0){
                left = ExprVar.make(null, fromExprStr);
                if (transition.parentConcState.isParameterized) left = ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "p"), left);
                Expr right = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "conf"));
                binaryFrom = ExprBinary.Op.IN.make(null, null, left, mult(right));
        	}     			
        	
        	if(binaryFrom == null) {
        		Expr right = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "conf"));
        		Expr source = ExprVar.make(null, fromExprStr);
        		if (transition.parentConcState.isParameterized) source = ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "p"), source);
        		binaryFrom = ExprBinary.Op.IN.make(null, null, source, mult(right));
        	}	
        }

        expression = binaryFrom;

        isCreatingEnabledAfterPred = true;
        
        /* Creating the following expression: AND[whenExpr, whenExpr, ..] */
        if (transition.whenExpr != null && transition.whenExpr.exprList != null) {           	
            Expr modifiedExpr = getVarFromParentExpr(transition.whenExpr.expr, getParentConcState(transition.parentState), module);
            	
            if (expression == null)
                expression = ExprBinary.Op.AND.make(null, null, binaryFrom, modifiedExpr);
            else
                expression = ExprBinary.Op.AND.make(null, null, expression, modifiedExpr);
            
        }

        isCreatingEnabledAfterPred = false;

        return expression;
    }
    
    /****************************************** POST CONDITION PREDICATE ***************************************/

    /*
     * This function creates the AST for the postcondition predicate in the Alloy
     * Model
     */
    private static void createPostConditionAST(DashTrans transition, DashModule module) {
    	System.out.println("\nTransition: " + transition.modifiedName);
        Expr sStable = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "stable"));
        Expr sPrimeStable = ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), ExprVar.make(null, "stable"));
        Expr sEvents = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "events"));
        Expr sPrimeEvents = ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), ExprVar.make(null, "events"));
        ExprVar intEvent = ExprVar.make(null, "InternalEvent");
    	DashConcState parent = getParentConcState(transition.parentState);
        Expr expression = null;

        /*
         * Creating the following expression: s_next.conf = s.conf - sourceState +
         * destinationState
         */
        if (transition.gotoExpr.gotoExpr.size() > 0) {
        	String gotoExprStr = transition.gotoExpr.gotoExpr.get(0).replace('/', '_');
            
            String fromExprStr = "";
            if(DashToCoreDash.getStateFromName(transition.fromExpr.fromExpr.get(0), module) != null)
            	fromExprStr = DashToCoreDash.getStateFromName(transition.fromExpr.fromExpr.get(0), module).modifiedName;
            else
            	fromExprStr = transition.fromExpr.fromExpr.get(0).replace('/', '_');
            
            Expr fromExpr = null;
            Expr gotoExpr = null;
            if (transition.parentConcState.isParameterized) {
            	fromExpr = ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "p"), ExprVar.make(null, DashHelper.toLowerCase(fromExprStr)));
            	if (transition.gotoExpr.param == null) {
            		gotoExpr = ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "p"), ExprVar.make(null, DashHelper.toLowerCase(gotoExprStr)));
            	}
            	else {
            		gotoExpr = ExprBinary.Op.JOIN.make(null, null, ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "p"), ExprVar.make(null, transition.gotoExpr.param)), ExprVar.make(null, DashHelper.toLowerCase(gotoExprStr)));
            	}
            }
            else {
            	fromExpr = ExprVar.make(null, fromExprStr);
            	gotoExpr = ExprVar.make(null, gotoExprStr);
            }
            
            Expr sConf = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "conf")); //s.conf
            Expr sConfPrime = ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), ExprVar.make(null, "conf"));//s_next.conf
            Expr binaryRight = ExprBinary.Op.PLUS.make(null, null, ExprBinary.Op.MINUS.make(null, null, sConf, fromExpr), gotoExpr);//s.conf - fromExpr + gotoExpr
            expression = ExprBinary.Op.EQUALS.make(null, null, sConfPrime, binaryRight); //s_next.conf = s.conf - fromExpr + gotoExpr
        }

        /* Creating the following expression: AND[doexpr, doexpr, ..] */
        if (transition.doExpr != null && transition.doExpr.exprList != null) {                    
            Expr modifiedExpr = getVarFromParentExpr(transition.doExpr.expr, getParentConcState(transition.parentState), module);                 
            expression = ExprBinary.Op.AND.make(null, null, expression, modifiedExpr);
            //These are the variables that have not been changed in the post-cond and they need to retain their values in the next snapshot
            Map<String, DashConcState> unchangedVars = new LinkedHashMap<String, DashConcState>(getUnchangedVars(transition.doExpr.exprList, module));
            for (String var : unchangedVars.keySet()) {
            	//System.out.println("Changing: " + var);
                expression = ExprBinary.Op.AND.make(null, null, expression, createUnchangedVariableAST(var, unchangedVars.get(var), parent));
            }
            // If we refer to a variable in a different replicated component and change it, we need to ensure this variable remains the same for the remaining components
            // E.g. ConcState[ref]/variable' = Expr
            expression = constrainVarsChangedByReference(expression);
            /*
            for (String var: paramVarRef.keySet()) {
            	expression = ExprBinary.Op.AND.make(null, null, expression, constrainChangedRefParamVar(var, changedVars.get(var), paramVarRef.get(var)));
            	System.out.println("Expr: " + constrainChangedRefParamVar(var.toString(), changedVars.get(var), paramVarRef.get(var)));
            }
            */
            for (String var: localBufferChanged.keySet()) {
            	expression = ExprBinary.Op.AND.make(null, null, expression, constrainChangedBuffer(var, changedVars.get(var), localBufferChanged.get(var)));
            	//System.out.println("Buffer: " + var + " Parent: " + changedVars.get(var).param + " Ref: " + localBufferChanged.get(var));
            }
            //If we have changed a var in this replicated conc state, we need to ensure that the remaining replicated conc states do not change this var
            if (transition.parentConcState.isParameterized) {
	            for (String var : changedBinaryVars.keySet()) {
	            	if(changedBinaryVars.get(var).modifiedName.equals(transition.parentConcState.modifiedName)) {
	                	//System.out.println("Changing2: " + var);
	            		expression = ExprBinary.Op.AND.make(null, null, expression, constrainChangedParamVar(var, changedBinaryVars.get(var)));
	            		//System.out.println("Expression: " + constrainChangedParamVar(var, changedBinaryVars.get(var)));
	            	}
	            }
	            for (String var : changedUnaryVars.keySet()) {
	            	if(changedUnaryVars.get(var).modifiedName.equals(transition.parentConcState.modifiedName)) 
	                	//System.out.println("Changing3: " + var);
	            		expression = ExprBinary.Op.AND.make(null, null, expression, constrainChangedParamVar(var, changedUnaryVars.get(var)));
	            }
            }
            clearVarChangeContainers();
        }
        
        /* Creating the following expression(s): s_next.variable = s.variable */
        if (transition.doExpr == null) {
            //These are the variables that have not been changed in the post-cond and they need to retain their values in the next snapshot
            Map<String, DashConcState> unchangedVars = new LinkedHashMap<String, DashConcState>(getUnchangedVars(null, module));
            for (String var : unchangedVars.keySet()) {
                expression = ExprBinary.Op.AND.make(null, null, expression, createUnchangedVariableAST(var, unchangedVars.get(var), parent));
            }
            changedVars.clear();
        }

        /*
         * Creating the following expression: testIfNextStable[s, s_next, {none},
         * Mutex_Process1_wait] => { s_next.stable = True } else { s_next.stable = False }
         */
        if (module.stateHierarchy && !DashOptions.isEnvEventModel) {
            Expr ifExpr = ExprBinary.Op.EQUALS.make(null, null, ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), ExprVar.make(null, "stable")), ExprVar.make(null, "True"));
            Expr ElseExpr = ExprBinary.Op.EQUALS.make(null, null, ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), ExprVar.make(null, "stable")), ExprVar.make(null, "False"));
            Expr ifCond = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "testIfNextStable"));
            ifCond = ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), ifCond);
            if (!transition.parentConcState.isParameterized)
            	ifCond = ExprBadJoin.make(null, null, ExprVar.make(null, transition.modifiedName), ifCond);
            else
            	ifCond = ExprBadJoin.make(null, null, ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "p"), ExprVar.make(null, DashHelper.toLowerCase(transition.modifiedName))), ifCond);
            ifCond = ExprBadJoin.make(null, null, ExprVar.make(null, "none"), ifCond);
            
            /* Conjunction of any env variables in the model */
            for(String concStateName: module.envVariableNames.keySet()) {
            	for(String envVar: module.envVariableNames.get(concStateName)) {
            		Expr leftJoin = ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), ExprVar.make(null, concStateName + "_" + envVar));
            		Expr rightJoin = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, concStateName + "_" + envVar));
            		Expr equals = ExprBinary.Op.EQUALS.make(null, null, leftJoin, rightJoin);
            		ElseExpr = ExprBinary.Op.AND.make(null, null, ElseExpr, equals);
            	}
            }
            
            Expr ifElseExpr = ExprITE.make(null, ifCond, ifExpr, ElseExpr);
            expression = ExprBinary.Op.AND.make(null, null, expression, ifElseExpr);
        }

        /*
         * Creating the following expression: testIfNextStable[s, s_next, {none},
         * Elevator_Controller_sendReq] => { s_next.stable = True s.stable = True => { no
         * ((s_next.events & InternalEvent) ) } else { no ((s_next.events & InternalEvent) - {
         * (InternalEvent & s.events)}) } } else { s_next.stable = False s.stable = True =>
         * { s_next.events & InternalEvent = {none}/sendExpr s_next.events & EnvironmentEvent = s.events
         * & EnvironmentEvent } else { s_next.events = s.events + {none}/sendExpr } }
         */
        if (module.stateHierarchy && DashOptions.isEnvEventModel) {
        	String sendCommand = transition.sendExpr == null ? "" : transition.sendExpr.name.replace('/', '_');
            Expr sPrimeStableTrue = ExprBinary.Op.EQUALS.make(null, null, sPrimeStable, ExprVar.make(null, "True")); //s_next.stable = True
            Expr sPrimeStableFalse = ExprBinary.Op.EQUALS.make(null, null, sPrimeStable, ExprVar.make(null, "False")); //s_next.stable = False
            Expr sStableTrue = ExprBinary.Op.EQUALS.make(null, null, sStable, ExprVar.make(null, "True")); //s.stable = True
            Expr sPrimeEnvAndIntEvn = ExprBinary.Op.INTERSECT.make(null, null, sPrimeEvents, intEvent); //s_nextevents & InternalEvent
            if(transition.sendExpr != null && transition.sendExpr.name != null) {
            	Expr right = null;
            	if (transition.sendExpr.parent.isParameterized && transition.sendExpr.param == null) { // For parameterized events (p.eventName)
            		right = ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "p"), ExprVar.make(null, DashHelper.toLowerCase(sendCommand)));
            	}
            	else if(transition.sendExpr.parent.isParameterized && transition.sendExpr.param != null) {
            		right = ExprBinary.Op.JOIN.make(null, null, ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "p"), ExprVar.make(null, transition.sendExpr.param)), ExprVar.make(null, DashHelper.toLowerCase(sendCommand)));
            	}
            	else {
            		right = ExprVar.make(null, sendCommand);
            	}
            	sPrimeEnvAndIntEvn = ExprBinary.Op.MINUS.make(null, null, sPrimeEnvAndIntEvn, right); //s_nextevents & InternalEvent - sendEvent
            }
            
            Expr sEnvAndIntEvn = ExprBinary.Op.INTERSECT.make(null, null, intEvent, sEvents); //s.events & InternalEvent
            Expr noSPrimeEnvAndIntEvn = ExprUnary.Op.NO.make(null, sPrimeEnvAndIntEvn); //no (s_nextevents & InternalEvent)
            
            Expr noSPrimeEnvAndIntEvnMinus = null; 
            if(transition.sendExpr != null && transition.sendExpr.name != null) //If there is a send command
            	noSPrimeEnvAndIntEvnMinus= ExprUnary.Op.NO.make(null, ExprBinary.Op.PLUS.make(null, null, sPrimeEnvAndIntEvn, sEnvAndIntEvn)); // no ((s_nextevents & InternalEvent) - sendEvent + (s.events & InternalEvent))
            else
            	noSPrimeEnvAndIntEvnMinus= ExprUnary.Op.NO.make(null, ExprBinary.Op.MINUS.make(null, null, sPrimeEnvAndIntEvn, sEnvAndIntEvn)); // no ((s_nextevents & InternalEvent) - (s.events & InternalEvent))
            
            Expr ifLowerExpr = ExprITE.make(null, sStableTrue, noSPrimeEnvAndIntEvn, noSPrimeEnvAndIntEvnMinus);

            ifLowerExpr = ExprBinary.Op.AND.make(null, null, sPrimeStableTrue, ifLowerExpr);

            Expr elseLowerExprIf = null;
            if(transition.sendExpr != null && transition.sendExpr.name != null) {//If there is a send command 
            	Expr right = null;
            	if (transition.sendExpr.parent.isParameterized && transition.sendExpr.param == null) { // For parameterized events (p.eventName)
            		right = ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "p"), ExprVar.make(null, DashHelper.toLowerCase(sendCommand)));
            	}
            	else if(transition.sendExpr.parent.isParameterized && transition.sendExpr.param != null) {
            		right = ExprBinary.Op.JOIN.make(null, null, ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "p"), ExprVar.make(null, transition.sendExpr.param)), ExprVar.make(null, DashHelper.toLowerCase(sendCommand)));
            	}
            	else {
            		right = ExprVar.make(null, sendCommand);
            	}
            	elseLowerExprIf = ExprBinary.Op.EQUALS.make(null, null, ((ExprBinary) sPrimeEnvAndIntEvn).left, right); //s_next.events & InternalEvent = {sendEvent}
            }
            else {
            	elseLowerExprIf = ExprBinary.Op.EQUALS.make(null, null, sPrimeEnvAndIntEvn, ExprVar.make(null, "none")); //s_next.events & InternalEvent = {none}
            }
             
            Expr sPrimeEvtAndEnv = ExprBinary.Op.INTERSECT.make(null, null, sPrimeEvents, ExprVar.make(null, "EnvironmentEvent")); //s_next.events & EnvironmentEvent
            Expr sEventAndEnv = ExprBinary.Op.INTERSECT.make(null, null, sEvents, ExprVar.make(null, "EnvironmentEvent")); //s.events & EnvironmentEvent
            elseLowerExprIf = ExprBinary.Op.AND.make(null, null, elseLowerExprIf, ExprBinary.Op.EQUALS.make(null, null, sPrimeEvtAndEnv, sEventAndEnv));

            Expr elseLowerElse = null;
            if(transition.sendExpr != null && transition.sendExpr.name != null) {//If there is a send command
            	Expr right = null;
            	if (transition.sendExpr.parent.isParameterized && transition.sendExpr.param == null) { // For parameterized events (p.eventName)
            		right = ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "p"), ExprVar.make(null, DashHelper.toLowerCase(sendCommand)));
            	}
            	else if(transition.sendExpr.parent.isParameterized && transition.sendExpr.param != null) {
            		right = ExprBinary.Op.JOIN.make(null, null, ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "p"), ExprVar.make(null, transition.sendExpr.param)), ExprVar.make(null, DashHelper.toLowerCase(sendCommand)));
            	}
            	else {
            		right = ExprVar.make(null, sendCommand);
            	}
            	elseLowerElse = ExprBinary.Op.EQUALS.make(null, null, sPrimeEvents, ExprBinary.Op.PLUS.make(null, null, sEvents, right)); //s_next.events = s.events + sendExpr
            }
            else {
            	elseLowerElse = ExprBinary.Op.EQUALS.make(null, null, sPrimeEvents, ExprBinary.Op.PLUS.make(null, null, sEvents, ExprVar.make(null, "none"))); //s_next.events = s.events + none
            }
            
            Expr elseLowerExpr = ExprITE.make(null, sStableTrue, elseLowerExprIf, elseLowerElse);
            elseLowerExpr = ExprBinary.Op.AND.make(null, null, sPrimeStableFalse, elseLowerExpr);
            
            /* Conjunction of any env variables in the model 
             * s_next.envVar = s.envVar
             */
            for(String concStateName: module.envVariableNames.keySet()) {
            	for(String envVar: module.envVariableNames.get(concStateName)) {
            		Expr leftJoin = ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), ExprVar.make(null, concStateName + "_" + envVar));
            		Expr rightJoin = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, concStateName + "_" + envVar));
            		Expr equals = ExprBinary.Op.EQUALS.make(null, null, leftJoin, rightJoin);
            		elseLowerExpr = ExprBinary.Op.AND.make(null, null, elseLowerExpr, equals);
            	}
            }
         
            Expr tFuncCall = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "testIfNextStable")); //s.testIfNextStable
            Expr genEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), tFuncCall); //s_next.s.enabledAfterStep_transName
            Expr sPrimeGenEventT = ExprBadJoin.make(null, null, ExprVar.make(null, transition.modifiedName), genEventT); //tranName.s_next.s.enabledAfterStep_transName
            Expr ssPrimeGenEventT = null;
            if(transition.sendExpr != null && transition.sendExpr.name != null) {
            	Expr right = null;
            	if (transition.sendExpr.parent.isParameterized && transition.sendExpr.param == null) { // For parameterized events (p.eventName)
            		right = ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "p"), ExprVar.make(null, DashHelper.toLowerCase(sendCommand)));
            	}
            	else if(transition.sendExpr.parent.isParameterized && transition.sendExpr.param != null) {
            		right = ExprBinary.Op.JOIN.make(null, null, ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "p"), ExprVar.make(null, transition.sendExpr.param)), ExprVar.make(null, DashHelper.toLowerCase(sendCommand)));
            	}
            	else {
            		right = ExprVar.make(null, sendCommand);
            	}
            	ssPrimeGenEventT = ExprBadJoin.make(null, null, right, sPrimeGenEventT); // sendEventName.tranName.s_next.s.enabledAfterStep_transName
            }
            else {
            	ssPrimeGenEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "none"), sPrimeGenEventT); // none.tranName.s_next.s.enabledAfterStep_transName
            }
            
            expression = ExprBinary.Op.AND.make(null, null, expression, ExprITE.make(null, ssPrimeGenEventT, ifLowerExpr, elseLowerExpr));
        }
        
        /* Creating the following expression: no (s_next.events & InternalEvent) */
        Expr sendExpr = null;
        if (transition.sendExpr == null && DashOptions.isEnvEventModel && !module.stateHierarchy) {
            Expr join = ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), ExprVar.make(null, "events")); // s_next.events
            Expr rightBinary = ExprBinary.Op.INTERSECT.make(null, null, join, ExprVar.make(null, "InternalEvent")); // s_next.events & InternalEvent
            sendExpr = ExprUnary.Op.NO.make(null, rightBinary); // no (s_next.events & InternalEvent)
        }
        /* Creating the following expression: sentEvent in s_next.events */
        if (transition.sendExpr != null && transition.sendExpr.name != null) {
            Expr join = ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), ExprVar.make(null, "events")); // s_next.events
            Expr right = null;
            String sendCommand = transition.sendExpr == null ? "" : transition.sendExpr.name.replace('/', '_');
        	if (transition.sendExpr.parent.isParameterized && transition.sendExpr.param == null) { // For parameterized events (p.eventName)
        		right = ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "p"), ExprVar.make(null, DashHelper.toLowerCase(sendCommand)));
        	}
        	else if(transition.sendExpr.parent.isParameterized && transition.sendExpr.param != null) {
        		right = ExprBinary.Op.JOIN.make(null, null, ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "p"), ExprVar.make(null, transition.sendExpr.param)), ExprVar.make(null, DashHelper.toLowerCase(sendCommand)));
        	}
        	else {
        		right = ExprVar.make(null, sendCommand);
        	}
            sendExpr = ExprBinary.Op.IN.make(null, null, right, mult(join)); // sentEvent in s_next.events
        }

        if (sendExpr != null)
            expression = ExprBinary.Op.AND.make(null, null, expression, sendExpr);
        
        /* For managing Enter/Exit commands */        
        DashState destinationState = getState(transition.gotoExpr.gotoExpr.get(0).replace('/', '_'), module);
        if(transition.gotoExpr.gotoExpr.size() > 0 && destinationState != null) {        	
        	Expr gotoExpr = ExprVar.make(null, transition.gotoExpr.gotoExpr.get(0).replace('/', '_'));
        	Expr enterCall = ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), ExprVar.make(null, "enter_" + gotoExpr.toString()));
        	
        	if(destinationState.enter.size() > 0) {
        		expression = ExprBinary.Op.AND.make(null, null, expression, enterCall);
        	}
        } 
        
        DashState sourceState = getParentSourceState(transition, module);
        expression = createExitAST(expression, sourceState, transition);
                
        expression = ExprUnary.Op.NOOP.make(null, expression);
       
        if (transition.parentConcState.isParameterized)
        	addParameterizedPredicateAST(module, "pos_" + transition.modifiedName, "s", "s_next", null, null, transition.parentConcState.param, expression);
        else
        	addPredicateAST(module, "pos_" + transition.modifiedName, "s", "s_next", null, null, expression);
    }
    
    private static void clearVarChangeContainers() {
        paramVarRef.clear();
        changedBinaryVars.clear();
        changedUnaryVars.clear();
        localBufferChanged.clear();
        changedVars.clear();
    }
    
    /****************************************** SEMANTICS PREDICATE ***************************************/

    /*
     * This function creates the AST for the Semantics predicate in the Alloy Model
     */
    private static void createSemanticsAST(DashTrans transition, DashModule module) {
        Expr expression = null;
        Expr transNameExpr = transition.parentConcState.isParameterized ? ExprVar.make(null, DashHelper.toLowerCase(transition.modifiedName)) : ExprVar.make(null, (transition.modifiedName));

        /* Creating the following expression: s_next.taken = currentTrans */
        Expr semanticsExpr = null;
        Expr sTakenPrime = ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), ExprVar.make(null, "taken")); //s_next.taken
        Expr sTaken = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "taken")); //s.taken
        if (!module.stateHierarchy) {
            semanticsExpr = ExprBinary.Op.EQUALS.make(null, null, sTakenPrime, ExprVar.make(null, transition.modifiedName)); //s_next.taken = currentTrans
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
         * Creating the following expression: s.stable = True => (s_next.taken + transName)
         * else { )
         */
        Expr ifElseExpr = null;
        if (module.stateHierarchy) {
            Expr ifCond = ExprBinary.Op.EQUALS.make(null, null, ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "stable")), ExprVar.make(null, "True")); //s.stable = True
            Expr ifExpr = transition.parentConcState.isParameterized ? ExprBinary.Op.EQUALS.make(null, null, sTakenPrime, ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "p"), transNameExpr)) : //s_next.taken = p.currentTrans 
            	ExprBinary.Op.EQUALS.make(null, null, sTakenPrime, transNameExpr); //s_next.taken = currentTrans
            Expr ElseExprLeft = transition.parentConcState.isParameterized ? ExprBinary.Op.EQUALS.make(null, null, sTakenPrime, ExprBinary.Op.PLUS.make(null, null, sTaken, ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "p"), transNameExpr))) : //s_next.taken = s.taken + p.transName
            		ExprBinary.Op.EQUALS.make(null, null, sTakenPrime, ExprBinary.Op.PLUS.make(null, null, sTaken, transNameExpr)); // s_next.taken = s.taken + transName
            Expr ElseExprRight = null;
            Expr ElseRightBinPlus = null;
            for (DashTrans trans : module.transitions.values()) {
                if (getParentConcState(trans.parentState).modifiedName.equals(getParentConcState(transition.parentState).modifiedName)) {
                	String transitionName = trans.parentConcState.isParameterized ? DashHelper.toLowerCase(trans.modifiedName) : trans.modifiedName;
                    if (ElseRightBinPlus == null)
                        ElseRightBinPlus = trans.parentConcState.isParameterized ? ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "p"), ExprVar.make(null, transitionName)) : ExprVar.make(null, transitionName);
                    else
                        ElseRightBinPlus = trans.parentConcState.isParameterized ? ExprBinary.Op.PLUS.make(null, null, ElseRightBinPlus, ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "p"), ExprVar.make(null, transitionName))) : ExprBinary.Op.PLUS.make(null, null, ElseRightBinPlus, ExprVar.make(null, transitionName));
                }
            }
            ElseExprRight = ExprBinary.Op.INTERSECT.make(null, null, sTaken, ElseRightBinPlus); //no (s.taken & transNames)
            ElseExprRight = ExprUnary.Op.NO.make(null, ElseExprRight);
            Expr ElseExpr = ExprBinary.Op.AND.make(null, null, ElseExprLeft, ElseExprRight);
            ifElseExpr = ExprITE.make(null, ifCond, ifExpr, ElseExpr);                      
            expression = ifElseExpr;
            
        	if(transition.parentState instanceof DashState && ((DashState) transition.parentState).states.size() > 0){
        		for(DashState state: ((DashState) transition.parentState).states)
        			getInnerTransitions(state, innerTransitions);	
        	}
        	
        	for(DashTrans trans: innerTransitions) 
        		expression = ExprBinary.Op.AND.make(null, null, expression, ExprUnary.Op.NOT.make(null, ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "pre_" + trans.modifiedName))));
        }

        expression = ExprUnary.Op.NOOP.make(null, expression);
        
        if (transition.parentConcState.isParameterized)
        	addParameterizedPredicateAST(module, "semantics_" + transition.modifiedName, "s", "s_next", null, null, transition.parentConcState.param, expression);
        else
        	addPredicateAST(module, "semantics_" + transition.modifiedName, "s", "s_next", null, null, expression);
    }
    
    /****************************************** TRANSITION CALL PREDICATE ***************************************/

    /*
     * This function creates the AST for the transition call (the one that refers to
     * the pre,post,semantics) predicate in the Alloy Model
     */
    private static void createTransCallAST(DashTrans transition, DashModule module) {
        ExprVar s = ExprVar.make(null, "s");
        ExprVar p = ExprVar.make(null, "p");
        ExprVar sPrime = ExprVar.make(null, "s_next");

        Expr expression = null;

        /*
         * Creating the following expressions: post_transName[s, s_next],
         * semantics_transName[s, s_next], pre_transName[s]
         */
        Expr preTransCall = ExprBadJoin.make(null, null, s, ExprVar.make(null, "pre_" + transition.modifiedName)); //s.pre_transName
        if (transition.parentConcState.isParameterized) preTransCall = ExprBadJoin.make(null, null, p, preTransCall); //p.s.pre_transName (For Parameterized Concurrent States)
        
        Expr postTransCall = ExprBadJoin.make(null, null, s, ExprVar.make(null, "pos_" + transition.modifiedName)); //s.post_transName
        postTransCall = ExprBadJoin.make(null, null, sPrime, postTransCall); //s_next.s.post_transName
        if (transition.parentConcState.isParameterized) postTransCall = ExprBadJoin.make(null, null, p, postTransCall); //p.s_next.s.post_transName (For Parameterized Concurrent States)
        
        expression = ExprBinary.Op.AND.make(null, null, preTransCall, postTransCall); //AND[postTransCall, semanticsCall]

        Expr sematicsCall = ExprBadJoin.make(null, null, s, ExprVar.make(null, "semantics_" + transition.modifiedName)); //s.sematics_transName
        sematicsCall = ExprBadJoin.make(null, null, sPrime, sematicsCall); //s_next.s.sematics_transName
        if (transition.parentConcState.isParameterized) sematicsCall = ExprBadJoin.make(null, null, p, sematicsCall); //p.s_next.s.semantics_transName (For Parameterized Concurrent States)

        expression = ExprBinary.Op.AND.make(null, null, expression, sematicsCall); //AND[postTransCall, semanticsCall, preTransCall]
        
        if (transition.parentConcState.isParameterized)
        	addParameterizedPredicateAST(module, transition.modifiedName, "s", "s_next", null, null, transition.parentConcState.param, expression); // (For Parameterized Concurrent States)
        else
        	addPredicateAST(module, transition.modifiedName, "s", "s_next", null, null, expression);
    }
    
    /****************************************** ENABLED AFTER STEP PREDICATE ***************************************/

    /*
     * This function creates an AST for the following predicate: pred
     * enabledAfterStep_transName[_s, s: Snapshot] {expressions}
     */
    private static void createEnabledNextStepAST(DashTrans transition, DashModule module) {
        Expr expr = null;
        if (module.stateHierarchy) {
            expr = getPreCondForEnabled(transition, module); //Store all the pre-conditions

            Expr ifCond = ExprBinary.Op.EQUALS.make(null, null, ExprBadJoin.make(null, null, ExprVar.make(null, "_s"), ExprVar.make(null, "stable")), ExprVar.make(null, "True")); //s.stable = True
            Expr ifExprLeft = ExprVar.make(null, "t");
            Expr ifExprRight = null;
            for (DashTrans trans : module.transitions.values()) {
                if (getParentConcState(trans.parentState).modifiedName.equals(getParentConcState(transition.parentState).modifiedName)) {
                    if (ifExprRight == null)
                        ifExprRight = trans.parentConcState.isParameterized ? ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "p"), ExprVar.make(null, DashHelper.toLowerCase(trans.modifiedName))) : ExprVar.make(null, trans.modifiedName);
                    else
                        ifExprRight = trans.parentConcState.isParameterized ? ExprBinary.Op.PLUS.make(null, null, ifExprRight, ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "p"), ExprVar.make(null, DashHelper.toLowerCase(trans.modifiedName)))) 
                        		: ExprBinary.Op.PLUS.make(null, null, ifExprRight, ExprVar.make(null, trans.modifiedName));
                }
            }
            Expr ifExpr = ExprBinary.Op.INTERSECT.make(null, null, ifExprLeft, ifExprRight);
            ifExpr = ExprUnary.Op.NO.make(null, ifExpr);

            String onCommand = transition.onExpr == null ? "" : transition.onExpr.name.replace('/', '_');
            if (DashOptions.isEnvEventModel && transition.onExpr != null && transition.onExpr.name != null) {
                Expr _sEvent = ExprBadJoin.make(null, null, ExprVar.make(null, "_s"), ExprVar.make(null, "events"));
                Expr binaryIntersect = ExprBinary.Op.INTERSECT.make(null, null, _sEvent, ExprVar.make(null, "EnvironmentEvent"));
                Expr binaryPlus = ExprBinary.Op.PLUS.make(null, null, binaryIntersect, ExprVar.make(null, "genEvents"));
                Expr left = transition.onExpr.parent.isParameterized ? ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "p"), ExprVar.make(null, DashHelper.toLowerCase(onCommand))) : ExprVar.make(null, onCommand);
                Expr binaryIn = ExprBinary.Op.IN.make(null, null, left, binaryPlus);
                ifExpr = ExprBinary.Op.AND.make(null, null, ifExpr, binaryIn);
            }
           
            Expr elseExpr = null;
            Expr elseExprLeft = ExprBinary.Op.PLUS.make(null, null, ExprBadJoin.make(null, null, ExprVar.make(null, "_s"), ExprVar.make(null, "taken")), ExprVar.make(null, "t")); //_s.taken + t
            Expr elseExprRight = null;
            for (DashTrans trans : module.transitions.values()) {
                if (getParentConcState(trans.parentState).modifiedName.equals(getParentConcState(transition.parentState).modifiedName)) {
                    if (elseExprRight == null) 
                        elseExprRight = trans.parentConcState.isParameterized ? ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "p"), ExprVar.make(null, DashHelper.toLowerCase(trans.modifiedName))) : ExprVar.make(null, trans.modifiedName);
                    else
                        elseExprRight = trans.parentConcState.isParameterized ? ExprBinary.Op.PLUS.make(null, null, elseExprRight, ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "p"), ExprVar.make(null, DashHelper.toLowerCase(trans.modifiedName)))) 
                        		: ExprBinary.Op.PLUS.make(null, null, elseExprRight, ExprVar.make(null, trans.modifiedName));
                }
            }
            elseExpr = ExprBinary.Op.INTERSECT.make(null, null, elseExprLeft, elseExprRight);
            elseExpr = ExprUnary.Op.NO.make(null, elseExpr);

            if (DashOptions.isEnvEventModel && transition.onExpr != null && transition.onExpr.name != null) {
                Expr _sEvent = ExprBadJoin.make(null, null, ExprVar.make(null, "_s"), ExprVar.make(null, "events"));
                Expr binaryPlus = ExprBinary.Op.PLUS.make(null, null, _sEvent, ExprVar.make(null, "genEvents"));
                Expr left = transition.onExpr.parent.isParameterized ? ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "p"), ExprVar.make(null, DashHelper.toLowerCase(onCommand))) : ExprVar.make(null, onCommand);
                Expr binaryIn = ExprBinary.Op.IN.make(null, null, left, binaryPlus);
                elseExpr = ExprBinary.Op.AND.make(null, null, elseExpr, binaryIn);
            }

            expr = ExprBinary.Op.AND.make(null, null, expr, ExprITE.make(null, ifCond, ifExpr, elseExpr));
            
            if (!transition.parentConcState.isParameterized)
            	addPredicateAST(module, "enabledAfterStep_" + transition.modifiedName, "_s", "s", "t", "genEvents", expr);
            else
            	addParameterizedPredicateAST(module, "enabledAfterStep_" + transition.modifiedName, "_s", "s", "t", "genEvents", transition.parentConcState.param, expr);
        }
    }
    
    /****************************************** STABLE PREDICATE ***************************************/
    
    /*
     * This function creates an AST for the following predicate: pred stable[s] {
     * s.stable }
     */
    private static void createStableAST(DashModule module) {
        Expr sStable = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "stable"));
        Expr sStableEqualsTrue = ExprBinary.Op.EQUALS.make(null, null, sStable, ExprVar.make(null, "True"));
        if (module.stateHierarchy) {
        	addPredicateAST(module, "stable", "s", null, null, null, sStableEqualsTrue);
        }
    }
    
    /****************************************** SMALL STEP PREDICATE ***************************************/
    
    /*
    *  This function creates an AST for the following predicate: pred operation[s,
    *  s_next: Snapshot] { expressions }
    */
    static void createSmallStepAST(DashModule module) {
        Expr expression = null;

        for (DashTrans trans : module.transitions.values()) {
            List<Decl> decls = new ArrayList<Decl>();
            List<ExprVar> a = new ArrayList<ExprVar>();
            a.add(ExprVar.make(null, "p"));
            decls.add(new Decl(null, null, null, null, a, mult(ExprVar.make(null, trans.parentConcState.param)))); //p: param
            if (expression == null) {
                Expr expr = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, trans.modifiedName));
                expr = ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), expr);
                expr = trans.parentConcState.isParameterized ? ExprQt.Op.ONE.make(null, null, decls, ExprBadJoin.make(null, null, ExprVar.make(null, "p"), expr)) : expr; // some p: param | transName[s, s_next, p]
                expression = expr;
            } else {
                Expr expr = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, trans.modifiedName));
                expr = ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), expr);
                expr = trans.parentConcState.isParameterized ? ExprQt.Op.ONE.make(null, null, decls, ExprBadJoin.make(null, null, ExprVar.make(null, "p"), expr)) : expr; // some p: param | transName[s, s_next, p]
                expression = ExprBinary.Op.OR.make(null, null, expression, expr);
            }
        }

        addPredicateAST(module, "small_step", "s", "s_next", null, null, expression);
    }
    
    /****************************************** PATH PREDICATE ***************************************/
    
    private static void createPathAST(DashModule module) {
        List<Decl> decls = new ArrayList<Decl>();
        ExprVar s = ExprVar.make(null, "s");
        ExprVar sPrime = ExprVar.make(null, "s_next");
        List<ExprVar> a = new ArrayList<ExprVar>(Arrays.asList(s)); //[s]
        Expr snapshot = ExprUnary.Op.ONE.make(null, ExprVar.make(null, "Snapshot"));
        Expr sNext = ExprBadJoin.make(null, null, s, ExprVar.make(null, "next")); //s.next

        Expr expression = null;

        decls.add(new Decl(null, null, null, null, a, mult(snapshot))); //s: Snapshot

        a = new ArrayList<ExprVar>(Arrays.asList(sPrime));

        decls.add(new Decl(null, null, null, null, a, mult(sNext))); //s_next: s.next

        Expr operationCall = ExprBadJoin.make(null, null, s, ExprVar.make(null, "small_step"));
        operationCall = ExprBadJoin.make(null, null, sPrime, operationCall); //s_next.s.operation

        expression = ExprQt.Op.ALL.make(null, null, decls, operationCall);

        expression = ExprBinary.Op.AND.make(null, null, expression, ExprBadJoin.make(null, null, ExprVar.make(null, "snapshot/first"), ExprVar.make(null, "init")));
        addPredicateAST(module, "path", null, null, null, null, expression);
    }
    
    /****************************************** TEST IF STABLE PREDICATE ***************************************/

    /*
     * This function creates an AST for the following predicate: pred
     * testIfNextStable[s, s_next: Snapshot, genEvents: set InternalEvent,
     * t:TransitionLabel] {}
     */
    private static void createTestIfStableAST(DashModule module) {
        Expr expr = null;

        for (DashTrans trans : module.transitions.values()) {
        	if (!trans.parentConcState.isParameterized) {
	            if (expr == null) {
	                Expr tFuncCall = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "enabledAfterStep_" + trans.modifiedName)); //t.enabledAfterStep_transName
	                Expr genEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), tFuncCall); //genEvents.t.enabledAfterStep_transName
	                Expr sPrimeGenEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "t"), genEventT);
	                if (DashOptions.isEnvEventModel) {
	                	Expr ssPrimeGenEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "genEvents"), sPrimeGenEventT);
	                	expr = ExprUnary.Op.NOT.make(null, ssPrimeGenEventT); //!enabledAfterStep_transName[s, s_next, t, genEvents]\n
	                }
	                else {
	                	expr = ExprUnary.Op.NOT.make(null, sPrimeGenEventT); //!enabledAfterStep_transName[s, s_next, t]\n
	                }
	            } else {
	                Expr tFuncCall = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "enabledAfterStep_" + trans.modifiedName)); //s.enabledAfterStep_transName
	                Expr genEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), tFuncCall); //s_next.s.enabledAfterStep_transName
	                Expr sPrimeGenEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "t"), genEventT);
	                if (DashOptions.isEnvEventModel) {
	                	Expr ssPrimeGenEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "genEvents"), sPrimeGenEventT);
	                    Expr negated = ExprUnary.Op.NOT.make(null, ssPrimeGenEventT); //!enabledAfterStep_transName[s, s_next, t, genEvents]\n
	                	expr = ExprBinary.Op.AND.make(null, null, expr, negated);
	                }
	                else {
	                    Expr negated = ExprUnary.Op.NOT.make(null, sPrimeGenEventT); //!enabledAfterStep_transName[s, s_next, t]\n
	                    expr = ExprBinary.Op.AND.make(null, null, expr, negated);
	                } 
	            }
        	}
        	else {
                List<Decl> decls = new ArrayList<Decl>();
                List<ExprVar> a = new ArrayList<ExprVar>();
                a.add(ExprVar.make(null, "p"));
                decls.add(new Decl(null, null, null, null, a, mult(ExprVar.make(null, trans.parentConcState.param)))); //p: param
	            if (expr == null) {
	                Expr tFuncCall = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "enabledAfterStep_" + trans.modifiedName)); //t.enabledAfterStep_transName
	                Expr genEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), tFuncCall); //genEvents.t.enabledAfterStep_transName
	                Expr sPrimeGenEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "t"), genEventT);
	                Expr ssPrimeGenEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "genEvents"), sPrimeGenEventT);
	                Expr ssPrimeGenEventTP = ExprBadJoin.make(null, null, ExprVar.make(null, "p"), ssPrimeGenEventT);
	                expr = ExprQt.Op.NO.make(null, null, decls, ssPrimeGenEventTP); // no p: param | enabledAfterStep_transName[s, s_next, t, genEvents, p]\n
	            } else {
	                Expr tFuncCall = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "enabledAfterStep_" + trans.modifiedName)); //s.enabledAfterStep_transName
	                Expr genEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), tFuncCall); //s_next.s.enabledAfterStep_transName
	                Expr sPrimeGenEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "t"), genEventT);
	                Expr ssPrimeGenEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "genEvents"), sPrimeGenEventT);
	                Expr ssPrimeGenEventTP = ExprBadJoin.make(null, null, ExprVar.make(null, "p"), ssPrimeGenEventT);
	                Expr quant = ExprQt.Op.NO.make(null, null, decls, ssPrimeGenEventTP); // no p: param | enabledAfterStep_transName[s, s_next, t, genEvents, p]\n
	                expr = ExprBinary.Op.AND.make(null, null, expr, quant);
	            }
        	}
        }

        /* No need to add this predicate if there are no transitions */
        if (module.transitions.keySet().size() > 0 && module.stateHierarchy) {
            expr = ExprUnary.Op.NOOP.make(null, expr);
            addPredicateAST(module, "testIfNextStable", "s", "s_next", "t", "genEvents", expr);
        }
    }

    /****************************************** IS ENABLED PREDICATE ***************************************/
    
    /*
     * This function creates an AST for the following predicate: pred isEnabled[s:
     * Snapshot] {}
     */
    static void createIsEnabledAST(DashModule module) {
        Expr expr = null;
        for (DashTrans trans : module.transitions.values()) {
            List<Decl> decls = new ArrayList<Decl>();
            List<ExprVar> a = new ArrayList<ExprVar>();
            a.add(ExprVar.make(null, "p"));
            decls.add(new Decl(null, null, null, null, a, mult(ExprVar.make(null, trans.parentConcState.param)))); //p: param
            if (expr == null) {
                expr = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "pre_" + trans.modifiedName)); //pre_transName[s]
                expr = trans.parentConcState.isParameterized ? ExprQt.Op.SOME.make(null, null, decls, ExprBadJoin.make(null, null, ExprVar.make(null, "p"), expr)) : expr; // some p: param | pre_transName[s, p]
            }	
            else {
                Expr preTransNameS = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "pre_" + trans.modifiedName));
                preTransNameS = trans.parentConcState.isParameterized ? ExprQt.Op.SOME.make(null, null, decls, ExprBadJoin.make(null, null, ExprVar.make(null, "p"), preTransNameS)) : preTransNameS; // some p: param | pre_transName[s, p]
                expr = ExprBinary.Op.OR.make(null, null, expr, preTransNameS);
            }
        }

        //No need to add this predicate if there are no transitions in the model
        if (module.transitions.keySet().size() > 0 && module.stateHierarchy) {
            addPredicateAST(module, "isEnabled", "s", null, null, null, expr);
        }
    }

    /****************************************** EQUALS PREDICATE ***************************************/
    
    /*
     * This function creates an AST for the following predicate: pred equals[s, s_next:
     * Snapshot] {}
     */
    private static void createEqualsAST(DashModule module) {
        ExprVar s = ExprVar.make(null, "s");
        ExprVar sPrime = ExprVar.make(null, "s_next");
        ExprVar conf = ExprVar.make(null, "conf");
        ExprVar events = ExprVar.make(null, "events");
        ExprVar taken = ExprVar.make(null, "taken");

        Expr expr = ExprBinary.Op.EQUALS.make(null, null, ExprBadJoin.make(null, null, sPrime, conf), ExprBadJoin.make(null, null, s, conf)); //s_next.conf = s.conf
        if (DashOptions.isEnvEventModel)
            expr = ExprBinary.Op.AND.make(null, null, expr, ExprBinary.Op.EQUALS.make(null, null, ExprBadJoin.make(null, null, sPrime, events), ExprBadJoin.make(null, null, s, events))); //s_next.events = s.events

        expr = ExprBinary.Op.AND.make(null, null, expr, ExprBinary.Op.EQUALS.make(null, null, ExprBadJoin.make(null, null, sPrime, taken), ExprBadJoin.make(null, null, s, taken))); //s_next.taken = s.taken
        
        /* Conjunction of any env variables in the model */
        for(String concStateName: module.envVariableNames.keySet()) {
        	for(String envVar: module.envVariableNames.get(concStateName)) {
        		Expr leftJoin = ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), ExprVar.make(null, concStateName + "_" + envVar));
        		Expr rightJoin = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, concStateName + "_" + envVar));
        		Expr equals = ExprBinary.Op.EQUALS.make(null, null, leftJoin, rightJoin);
        		expr = ExprBinary.Op.AND.make(null, null, expr, equals);
        	}
        }

        for (String key : module.variableNames.keySet()) {
            for (String var : module.variableNames.get(key))
                expr = ExprBinary.Op.AND.make(null, null, expr, ExprBinary.Op.EQUALS.make(null, null, ExprBadJoin.make(null, null, sPrime, ExprVar.make(null, key + "_" + var)), ExprBadJoin.make(null, null, s, ExprVar.make(null, key + "_" + var))));
        }

        expr = ExprUnary.Op.NOOP.make(null, expr);
        addPredicateAST(module, "equals", "s", "s_next", null, null, expr);
    }

    /****************************************** INIT PREDICATE ***************************************/
    
    /* This function creates the AST for the init conditions */
    private static void createInitAST(DashModule module) {
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        ExprVar snapshot = ExprVar.make(null, "Snapshot");
        ExprVar p = ExprVar.make(null, "p");
        a.add(p);

        ExprVar s = ExprVar.make(null, "s");
        ExprVar conf = ExprVar.make(null, "conf");
        ExprVar events = ExprVar.make(null, "events");
        ExprVar taken = ExprVar.make(null, "taken");
        ExprVar stable = ExprVar.make(null, "stable");
       
        Expr binaryLeft = ExprBadJoin.make(null, null, s, conf);
        Expr binaryRight = null;
        Expr expression = null;
        isCreatingInit = true;

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
        
        if (binaryRight != null)
            expression = ExprBinary.Op.EQUALS.make(null, null, binaryLeft, binaryRight);
        
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
                modifiedExpr = (init.parent.isParameterized && !(modifiedExpr instanceof ExprQt))? DashHelper.quantify("p", init.parent.param, modifiedExpr) : modifiedExpr;
                expression = ExprBinary.Op.AND.make(null, null, expression, modifiedExpr);
            }
        }
        
        a.clear();
        decls.clear();
        isCreatingInit = false;
        a.add(s);
        decls.add(new Decl(null, null, null, null, a, mult(snapshot))); //[s: Snapshot]
        expression = ExprUnary.Op.NOOP.make(null, expression);
        module.addFunc(null, null, "init", null, decls, null, expression);
    }

    /************************************ HELPER FUNCTION FOR CREATING PREDICATES *****************************************/
    
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

        if (a.size() > 0 && a.size() <= 2) { //Cannot add declarations if the predicate for no arguments
            decls.add(new Decl(null, null, null, null, a, mult(snapshot)));
        }
        else if (a.size() == 3) { //Only for EnabledAfterNextStep/testIfNextStable Predicate AST creation without EventLabel in the model
            decls.add(new Decl(null, null, null, null, new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, arg1), ExprVar.make(null, arg2))), mult(snapshot)));
            decls.add(new Decl(null, null, null, null, new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, arg3))), ExprVar.make(null, "TransitionLabel")));
        }
        else if (a.size() == 4) { //Only for EnabledAfterNextStep Predicate AST creation
            decls.add(new Decl(null, null, null, null, new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, arg1), ExprVar.make(null, arg2))), mult(snapshot)));
            decls.add(new Decl(null, null, null, null, new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, arg3))), ExprVar.make(null, "TransitionLabel")));
            decls.add(new Decl(null, null, null, null, new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, arg4))), mult(ExprUnary.Op.SETOF.make(null, ExprVar.make(null, "InternalEvent")))));
        }

        module.addFunc(null, null, predName, null, decls, null, expression);
    }
    
    /* Add a new Parameterized predicate to the Dash Module */
    private static void addParameterizedPredicateAST(DashModule module, String predName, String arg1, String arg2, String arg3, String arg4, String arg5, Expr expression) {
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
        if (a.size() == 4) { //Only for EnabledAfterNextStep Predicate AST creation
            decls.add(new Decl(null, null, null, null, new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, arg1), ExprVar.make(null, arg2))), mult(snapshot)));
            decls.add(new Decl(null, null, null, null, new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, arg3))), ExprVar.make(null, "TransitionLabel")));
            decls.add(new Decl(null, null, null, null, new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, arg4))), mult(ExprUnary.Op.SETOF.make(null, ExprVar.make(null, "InternalEvent")))));
        }
        
        if (arg5 != null)
        	decls.add(new Decl(null, null, null, null, new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "p"))), ExprVar.make(null, arg5))); 
        
        module.addFunc(null, null, predName, null, decls, null, expression);
    }
    
    /*************************** PARAMETERIZED CONSTRAINTS*****************************/
    
    // Creates the "constraints" fact to ensure that each replicated component has its own unique event, transition and state label
    private static void createParamConstFactAST(DashModule module) {
        Expr finalExpr = null;
    	
        for (DashConcState concState: module.concStates.values()) {
        	if (concState.isParameterized) {
        		Expr expr = null;
                List<Decl> decls = new ArrayList<Decl>();
                List<ExprVar> a = new ArrayList<ExprVar>();
        		List<String> states = new ArrayList<String>(getStates(concState));
        		List<String> transitions = new ArrayList<String>(getTransitions(module,concState));
        		List<String> events = new ArrayList<String>(getEvents(concState));
        		
        		for (String state: states) {
    				Expr left = ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "p"), ExprVar.make(null, DashHelper.toLowerCase(state))); 	//p.stateName
    				Expr right = ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "q"), ExprVar.make(null, DashHelper.toLowerCase(state)));	//q.stateName
    				Expr equals = ExprBinary.Op.NOT_EQUALS.make(null, null, left, right); //p.stateName != q.stateName
        			if(expr == null) {
        				expr = equals;
        			}
        			else {
        				expr = ExprBinary.Op.AND.make(null, null, expr, equals);
        			}
        		}
        		
        		for (String trans: transitions) {
    				Expr left = ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "p"), ExprVar.make(null, DashHelper.toLowerCase(trans)));  //p.transName
    				Expr right = ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "q"), ExprVar.make(null, DashHelper.toLowerCase(trans))); //q.transName
    				Expr equals = ExprBinary.Op.NOT_EQUALS.make(null, null, left, right); //p.transName != q.transName
        			if(expr == null) {
        				expr = equals;
        			}
        			else {
        				expr = ExprBinary.Op.AND.make(null, null, expr, equals);
        			}
        		}
        		
        		for (String event: events) {
    				Expr left = ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "p"), ExprVar.make(null, DashHelper.toLowerCase(event)));  //p.transName
    				Expr right = ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "q"), ExprVar.make(null, DashHelper.toLowerCase(event))); //q.transName
    				Expr equals = ExprBinary.Op.NOT_EQUALS.make(null, null, left, right); //p.eventName != q.eventName
        			if(expr == null) {
        				expr = equals;
        			}
        			else {
        				expr = ExprBinary.Op.AND.make(null, null, expr, equals);
        			}
        		}
        		
        		Expr b = ExprVar.make(null, concState.param);
        		a.add(ExprVar.make(null, "p"));
        		a.add(ExprVar.make(null, "q"));
        		decls.add(new Decl(null, new Pos("disj", 0, 0), null, null, a, mult(b)));
        		
        		if (finalExpr == null)
        			finalExpr = ExprQt.Op.ALL.make(null, null, decls, expr);
        		else
        			finalExpr = ExprBinary.Op.AND.make(null, null, finalExpr, ExprQt.Op.ALL.make(null, null, decls, expr));
        	}
        }
        
        if (finalExpr != null) {
        	module.addFact(null, "constraints", finalExpr);
        }
    }
    
    /****************************************** DIFFERENT ATOMS FACT ***************************************/
    
    static void createDifferentAtomsFact(DashModule module) {
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        Expr snapshot = ExprUnary.Op.ONE.make(null, ExprVar.make(null, "Snapshot"));
        Expr s = ExprVar.make(null, "s");
        Expr sPrime = ExprVar.make(null, "s_next");
        a.add((ExprVar) s);
        a.add((ExprVar) sPrime);
        decls.add(new Decl(null, null, null, null, a, mult(snapshot))); //s: Snapshot
        
        Expr equalsCall = ExprBadJoin.make(null, null, s, ExprVar.make(null, "equals"));//s.small_step
        equalsCall = ExprBadJoin.make(null, null, sPrime, equalsCall); //s_next.s.small_step
        Expr rightQT = ExprBinary.Op.IMPLIES.make(null, null, equalsCall, ExprBinary.Op.EQUALS.make(null, null, s, sPrime));
        Expr expr = ExprQt.Op.ALL.make(null, null, new ArrayList<Decl>(decls), rightQT); //all s, s_next: Snapshot | equals[s, s_next] => s = s_next
    	
        module.addFact(null, "different_atoms", expr);
    }
    
    /****************************************** BIG STEP FACT ***************************************/

    static void createBigStepFact(DashModule module) {
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        Expr s = ExprVar.make(null, "s");
        Expr sPrime = ExprVar.make(null, "s_next");
        Expr snapshot = ExprUnary.Op.ONE.make(null, ExprVar.make(null, "Snapshot"));
        Expr sStable = ExprBinary.Op.JOIN.make(null, null, s, ExprVar.make(null, "stable"));
        
        /*
         * Creating the following expression: (all s: Snapshot | !stable[s] => (one s_next: Snapshot | small_step[s, s_next]))
         */
        Expr notsStable = ExprUnary.Op.NOT.make(null, sStable); //!stable[s]
        Expr smallStepCall = ExprBadJoin.make(null, null, s, ExprVar.make(null, "small_step"));//s_next.small_step
        smallStepCall = ExprBadJoin.make(null, null, sPrime, smallStepCall); //s.s_next.small_step
        a.add((ExprVar) sPrime);
        decls.add(new Decl(null, null, null, null, a, mult(snapshot))); //s_next: Snapshot
        Expr qtExpr = ExprQt.Op.ONE.make(null, null, decls, smallStepCall);// one s_next: Snapshot | small_step[s, s_next]
        Expr imples = ExprBinary.Op.IMPLIES.make(null, null, notsStable, qtExpr); // !stable[s] => (one s_next: Snapshot | small_step[s, s_next])
        a.clear();
        decls.clear();
        a.add((ExprVar) s);
        decls.add(new Decl(null, null, null, null, a, mult(snapshot))); // s: Snapshot
        Expr expression = ExprQt.Op.ALL.make(null, null, decls, imples); // all s:Snapshot | !stable[s] => (one s_next: Snapshot | small_step[s, s_next])
        
        expression = ExprUnary.Op.NOOP.make(null, expression);
        module.addFact(null, "completeBigStep", expression);
    }
    
    /****************************************** REACHABILITY FACT ***************************************/
    
    static void createReachabilityFact(DashModule module) {
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        Expr snapshot = ExprUnary.Op.ONE.make(null, ExprVar.make(null, "Snapshot"));
        Expr s = ExprVar.make(null, "s");
        Expr sPrime = ExprVar.make(null, "s_next");

        /*
         * Creating the following expression: all s, s_next: Snapshot | s->s_next in Reachability.next
         * iff small_step[s, s_next]
         */
        a.add((ExprVar) s);
        a.add((ExprVar) sPrime);
        decls.add(new Decl(null, null, null, null, a, mult(snapshot))); //s, s_next: Snapshot
        Expr sArrowSPrime = ExprBinary.Op.ARROW.make(null, null, s, sPrime);
        Expr smallStepCall = ExprBadJoin.make(null, null, s, ExprVar.make(null, "small_step"));//s_next.small_step
        smallStepCall = ExprBadJoin.make(null, null, sPrime, smallStepCall); //s.s_next.small_step
        Expr rightQT = ExprBinary.Op.IFF.make(null, null, ExprBinary.Op.IN.make(null, null, sArrowSPrime, ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "Snapshot"), ExprVar.make(null, "next"))), smallStepCall);
        Expr expr = ExprQt.Op.ALL.make(null, null, new ArrayList<Decl>(decls), rightQT); //all s, s_next: Snapshot | s->s_next in Snapshot.nextStep iff small_step[s, s_next]

        expr = ExprUnary.Op.NOOP.make(null, expr);
        module.addFact(null, "reachabilityFact", expr);
    }
    
    /****************************************** TRACES FACT ***************************************/
    
    static void createTracesFact(DashModule module) {
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        Expr snapshot = ExprUnary.Op.ONE.make(null, ExprVar.make(null, "Snapshot"));
        Expr s = ExprVar.make(null, "s");
        a.add((ExprVar) s);
        
    	Expr expression = ExprBadJoin.make(null, null, ExprVar.make(null, "snapshot/first"), ExprVar.make(null, "init")); // init[first]
    	
    	Expr smallStep = ExprBadJoin.make(null, null, s, ExprVar.make(null, "small_step")); //small_step[s]
    	Expr sNext = ExprBinary.Op.JOIN.make(null, null, s, ExprVar.make(null, "next")); //s.next
    	smallStep = ExprBadJoin.make(null, null, sNext, smallStep); // small_step[s, s.next]
    	Expr notSinLast = ExprUnary.Op.NOT.make(null, ExprBinary.Op.IN.make(null, null, s, ExprVar.make(null, "snapshot/last"))); // !(s in last)
    	Expr implies = ExprBinary.Op.IMPLIES.make(null, null, notSinLast, smallStep); // !(s in last) => small_step[s, s.next]
    	decls.add(new Decl(null, null, null, null, a, mult(snapshot))); //s: Snapshot
    	Expr smallStepQuant = ExprQt.Op.ALL.make(null, null, decls, implies); // all s: Snapshot | !(s in last) => small_step[s, s.next]
    	expression = ExprBinary.Op.AND.make(null, null, expression, smallStepQuant);
    	decls.clear();
    	
        Expr iffLeft = ExprUnary.Op.NOT.make(null, ExprBadJoin.make(null, null, s, ExprVar.make(null, "stable"))); // ! stable[s] or s.stable = False
        Expr iffRight = ExprUnary.Op.SOME.make(null, ExprBadJoin.make(null, null, s, ExprVar.make(null, "snapshot/next")));
        Expr iffExpr = ExprBinary.Op.IMPLIES.make(null, null, iffLeft, iffRight);
    	decls.add(new Decl(null, null, null, null, a, mult(snapshot))); //s: Snapshot
        Expr quant = ExprQt.Op.ALL.make(null, null, decls, iffExpr); // all s: Snapshot | !stable[s] => some s.nextStep
        a.clear();
        decls.clear();
        
        if (module.stateHierarchy)
        	expression = ExprBinary.Op.AND.make(null, null, expression, quant);
        	
        module.addFact(null, "traces", expression);
    }
    
    /*************************************** KEEPING VARIABLES UNCHANGED ***************************************/
    
    private static Expr constrainChangedQuantifiedVar (Expr subExpr, DashConcState parent, DashModule module) {
    	for (String var: changedExprQtVars.keySet()) {		
    		List<String> quantifiers = new ArrayList<String>();
    		String paramName = changedExprQtVars.get(var).getParam();
            Expr binaryLeft = ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "quant"), ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), ExprVar.make(null, var)));  //p.(s_next.variableParent_varName)
            Expr binaryRight = ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "quant"), ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, var))); //s_next.variableParent_varName
            Expr binaryEquals = ExprBinary.Op.EQUALS.make(null, null, binaryLeft, binaryRight);
    		
        	for (Decl decl: exprQtDecls) {
        		String varName = parent.modifiedName + '_' + decl.expr;
        		if (decl.expr.toString().contains(paramName)) {
                	for(ExprHasName name: decl.names) 
                		quantifiers.add(name.toString());
        		}
        		else if (module.variable2Expression.containsKey(varName)) {
        			Expr quantExpr =  module.variable2Expression.get(varName);
        			String quantType = quantExpr instanceof ExprUnary ? ((ExprUnary) quantExpr).sub.toString() : "";
        			if (changedExprQtVars.get(var).getParam().equals(quantType)) {
                    	for(ExprHasName name: decl.names) 
                    		quantifiers.add(name.toString());
        			}
        		}
        	}
        	
            Expr param = ExprVar.make(null, paramName);
        	if (quantifiers.isEmpty()) { // A variable in the current parameterized concurrent state is changed
        		continue;
        	}
        	
        	for(String declName: quantifiers) {
        		param = ExprBinary.Op.MINUS.make(null, null, param, ExprVar.make(null, declName.toString()));
        	}
            
            List<Decl> decls = new ArrayList<Decl>();
            ExprVar q = ExprVar.make(null, "quant");
            List<ExprVar> a = new ArrayList<ExprVar>(Arrays.asList(q)); //[s]
            decls.add(new Decl(null, null, null, null, a, mult(param))); //p: param
            Expr expr = ExprQt.Op.ALL.make(null, null, decls, binaryEquals);
            //System.out.println("Adding: " + expr);
            subExpr = ExprBinary.Op.AND.make(null, null, subExpr, expr);
    	}
    	return subExpr;
    }
    
    private static Expr constrainVarsChangedByReference(Expr subExpr) {
    	for (String var: changedVarByReference.keySet()) {		
    		String paramName = changedVarByReference.get(var).getParam();
            Expr binaryLeft = ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "quant"), ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), ExprVar.make(null, var)));  //p.(s_next.variableParent_varName)
            Expr binaryRight = ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "quant"), ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, var))); //s_next.variableParent_varName
            Expr binaryEquals = ExprBinary.Op.EQUALS.make(null, null, binaryLeft, binaryRight);
    		
            Expr param = ExprVar.make(null, paramName);
        	
        	for(Expr ref: changedVarByReference.get(var).getReferences()) {
        		param = ExprBinary.Op.MINUS.make(null, null, param, ref);
        	}
            
            List<Decl> decls = new ArrayList<Decl>();
            ExprVar q = ExprVar.make(null, "quant");
            List<ExprVar> a = new ArrayList<ExprVar>(Arrays.asList(q)); //[s]
            decls.add(new Decl(null, null, null, null, a, mult(param))); //p: param
            Expr expr = ExprQt.Op.ALL.make(null, null, decls, binaryEquals);
            //System.out.println("Ref SubExpr: " + expr);
            subExpr = ExprBinary.Op.AND.make(null, null, subExpr, expr);
    	}
    	changedVarByReference.clear();
    	return subExpr;
    }
   
    //Find the variables that are unchanged during a transition
    static Map<String, DashConcState> getUnchangedVars(List<Expr> exprList, DashModule module) {
    	Map<String, DashConcState> unchangedVariables = new LinkedHashMap<String, DashConcState>(module.variable2ConcState);
      
        for (String var: changedVars.keySet()) {
        	if (unchangedVariables.keySet().contains(var))
        		unchangedVariables.remove(var);
        }
        
        return unchangedVariables;
    }
    
    /*
     * If a parameterized process has constrained its variable using Binary Equals, we need to ensure that the other processes do not
     * change that variable. Assuming that process p has changed its var, we write all quant: param | !(p in quant) => quant.s_next.var = quant.s.var 
     */
    private static Expr constrainChangedParamVar(String var, DashConcState varParent) {
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        Expr p = ExprVar.make(null, "p");
        Expr param = ExprBinary.Op.MINUS.make(null, null, ExprVar.make(null, varParent.param), p);//ExprUnary.Op.ONE.make(null, ExprVar.make(null, varParent.param));
        Expr quant = ExprVar.make(null, "quant");
        a.add((ExprVar) quant);
        decls.add(new Decl(null, null, null, null, a, mult(param))); //p: param
        

        Expr binaryLeft = ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), ExprVar.make(null, var)); 
        binaryLeft = ExprBadJoin.make(null, null, quant, binaryLeft); //quant.(s_next).var
        Expr binaryRight = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, var)); //quant.(s_next).var
        binaryRight = ExprBadJoin.make(null, null, quant, binaryRight);
        Expr binaryEquals = ExprBinary.Op.EQUALS.make(null, null, binaryLeft, binaryRight);
        
        return ExprQt.Op.ALL.make(null, null, decls, binaryEquals);
    }
    
    /*
     * This functions creates the AST for variables that are unchanged during a transition. 
     * If a varibale belongs to a parameterized Conc State, we create the following:
     * p.s_next.var = p'.s_next.var
     * If a varibale belongs to a parameterized Conc State and is not a varibale in the Conc State taking the transition, we create the following:
     * all p: param | p.s_next.var = p.s.var
     */
    private static Expr createUnchangedVariableAST(String var, DashConcState varConcState, DashConcState transConcState) {
        Expr binaryLeft = ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), ExprVar.make(null, var)); //s_next.variableParent_varName
        Expr binaryRight = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, var)); //s_next.variableParent_varName
        Expr binaryEquals = ExprBinary.Op.EQUALS.make(null, null, binaryLeft, binaryRight);

    	return binaryEquals;
    }
    
    /*************************************** MODIFY EXPRESSIONS WITH VARS ***************************************/

    //Take an expression in a do statement and modify any variables present. Eg: active_players should become
    //s.Game_active_players (Given that active_players is declared under the Game concurrent state)
    private static Expr modifyExprWithVar(Expr expr, DashConcState parent, DashModule module, Boolean isRef) {
    	DashConcState concState = new DashConcState(parent);
    	
        Expr expression = expr; 
        
        /* If the var refers to a parameterizerd concurrent process, return 'p' as this refers to the current process */
        if(expression.toString().equals("this")) {
        	return ExprVar.make(null, "p");
        }
    	
        //If we make a reference to a conc state outside of the current conc state, find it and 
        //modify the value of the expression accordingly
    	if(expr.toString().contains("/")) {
    		String concStateRef = expr.toString().substring(0, expr.toString().indexOf("/"));
    		DashConcState parentConcState = (parent.parent == null) ? parent : parent.parent;
    		for(DashConcState state: parentConcState.concStates) {    			
    			if(state.name.equals(concStateRef)) 
    				concState = new DashConcState(state);
    		}
    		expression = ExprVar.make(null, expr.toString().substring(expr.toString().indexOf("/") + 1));  
    		//System.out.println("Reference Expression: " + expression + " Full Expression: " + expr.toString());
    		return modifyExprWithVar(expression, concState, module, true);
    	} 
    	
        final List<String> variablesInParent = module.variableNames.get(concState.modifiedName);
        final List<String> envVariablesInParent = module.envVariableNames.get(concState.modifiedName);
        
        DashConcState outerConcState = concState.parent;

        if (variablesInParent != null)
            expression = modifyVar(expression, concState, expr, variablesInParent, false, isRef);
        if (envVariablesInParent != null)
            expression = modifyVar(expression, concState, expr, envVariablesInParent, true, isRef);

        while (outerConcState != null) {
            if (module.variableNames.get(outerConcState.modifiedName) != null)
                expression = modifyVar(expression, outerConcState, expr, module.variableNames.get(outerConcState.modifiedName), false, isRef);
            if (module.envVariableNames.get(outerConcState.modifiedName) != null)
                expression = modifyVar(expression, outerConcState, expr, module.envVariableNames.get(outerConcState.modifiedName), true, isRef);
            outerConcState = outerConcState.parent;
        }
        
        expression = replaceWithActionExpr(expression, concState, module);
        expression = replaceWithConditionExpr(expression, concState, module);
        
        return expression;
    }
    
    private static Expr modifyVar(Expr expression, DashConcState parent, Expr expr, List<String> exprList, boolean isEnvVar, boolean isRef) {
        for (String var : exprList) {
            if (expr.toString().equals(var + "'")) {
            	if (changingVar){
            		//System.out.println("Var: " + var + " ExprUnary? " + modifyingExprUnary);
            		String modifiedVarName = parent.modifiedName + '_' + var;
	            	changedVars.put(parent.modifiedName + '_' + var, parent); // Since the variable is primed, we add it to our list of changed variables
	            	if (modifyingExprQT.size() > 0 && parent.isParameterized) {
	            		(changedExprQtVars).put(modifiedVarName, new DashChangedVars(modifiedVarName, parent.isParameterized ? parent.param : null));
	            		//(changedQuantifiedVars).put(parent.modifiedName + '_' + var, parent); 
	            	}
	            	if (modifyingExprBinary && modifyingExprQT.size() == 0 && !isRef) {
	            		(changedBinaryVars).put(modifiedVarName, parent); 
	            	}
	            	if (modifyingExprUnary && modifyingExprQT.size() == 0 && !isRef) {
	            		(changedUnaryVars).put(modifiedVarName, parent); 
	            	}
            	}
            	if (parent.isParameterized && !isRef) { // No need to DotJoin the "p" expr if it is a reference to another parameterized concurrent state
            		return ExprBadJoin.make(null, null, ExprVar.make(null, "p"), ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "s_next"), ExprVar.make(null, parent.modifiedName + '_' + var)));
            	}
            	else {
            		refParamChanged = true;
            		return ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), ExprVar.make(null, parent.modifiedName + '_' + var));
            	}
            }
            else if (expr.toString().equals(var)) {
            	if(isCreatingEnabledAfterPred && isEnvVar) {
            		return ExprBadJoin.make(null, null, ExprVar.make(null, "_s"), ExprVar.make(null, parent.modifiedName + '_' + var));
            	}
            	else {
                	if (parent.isParameterized && !isRef && !(isCreatingInit && isCreatingExprQt) && !(isCreatingInvariant)) // No need to DotJoin the "p" expr if it is a reference to another parameterized concurrent state
                		return ExprBadJoin.make(null, null, ExprVar.make(null, "p"), ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, parent.modifiedName + '_' + var)));
                	else
                		return ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, parent.modifiedName + '_' + var));
            	}
            }
        }
        return expression;
    }
    
    /****************************** Retrieving Variables in Expressions *****************************/
    
    private static Expr getVarFromParentExpr(Object parentExpr, DashConcState parent, DashModule module) {    	
        if (parentExpr instanceof ExprBinary) {
            ExprBinary exprBinary = (ExprBinary) parentExpr;
            return getVarFromBinary(exprBinary, parent, module);
        }

        if (parentExpr instanceof ExprUnary) {
            ExprUnary unary = (ExprUnary) parentExpr;
            return getVarFromUnary(unary, parent, module, false);
        }
        
        if (parentExpr instanceof ExprBadJoin) {
        	return getVarFromBadJoin((ExprBadJoin) parentExpr, parent, module);
        }

        if (parentExpr instanceof ExprQt) {
            return getVarFromExprQt((ExprQt) parentExpr, parent, module, new ArrayList<Decl>(), false);
        }

        if (parentExpr instanceof ExprVar) {
        	return modifyExprWithVar((ExprVar) parentExpr, parent, module, false);
        }
        
        if (parentExpr instanceof ExprList) {
        	return getVarFromExprList((ExprList) parentExpr, parent, module, false);
        }
        
        if (parentExpr instanceof ExprConstant) {
        	return (Expr) parentExpr;
        }
        
        return null;
    }

    /*
     * Breakdown a binary expression into its subcomponents Example of a binary
     * expression: #varible1 = #variable2
     */
    private static Expr getVarFromBinary(ExprBinary binary, DashConcState parent, DashModule module) {
    	modifyingExprBinary = true;
    	Expr left = null, right = null;
        if (binary.left instanceof ExprUnary) {
            ExprUnary unary = (ExprUnary) binary.left;
            left = getVarFromUnary(unary, parent, module, false);
        }
        if (binary.left instanceof ExprVar) {
        	changingVar = (binary.op == ExprBinary.Op.EQUALS) ? true : false; // If the expression is ExprVar = Expression, then it is possible that a variable is being changed (if it is primed)
            left = modifyExprWithVar(binary.left, parent, module, false);
            changingVar = false;
        }
        if (binary.left instanceof ExprBinary) {
            left = getVarFromBinary((ExprBinary) binary.left, parent, module);
        }
        if (binary.left instanceof ExprBadJoin) {
        	changingVar = (binary.op == ExprBinary.Op.EQUALS) ? true : false; // If the expression is q.ExprVar = Expression, then it is possible that a variable is being changed (For parameterized variables)
            left = getVarFromBadJoin((ExprBadJoin) binary.left, parent, module);
            changingVar = false;
        }       
        if (binary.left instanceof ExprList) {
        	left = getVarFromExprList((ExprList) binary.left, parent, module, false);
        }
        if (binary.left instanceof ExprConstant) {
        	left = binary.left;
        }
        if (binary.left instanceof ExprList) {
        	left = getVarFromExprList((ExprList) binary.left, parent, module, false);
        }
        if (binary.left instanceof ExprQt) {
        	left = getVarFromExprQt((ExprQt) binary.left, parent, module, new ArrayList<Decl>(), false);
        }

        if (binary.right instanceof ExprUnary) {
            ExprUnary unary = (ExprUnary) binary.right;
            right = getVarFromUnary(unary, parent, module, false);
        }
        if (binary.right instanceof ExprVar) {
        	changingVar = binary.op == ExprBinary.Op.IN ? true : false; // If the expression is (Expression in var'), then it is possible that a variable (var) is being changed (if it is primed i.e var')
            right = modifyExprWithVar(binary.right, parent, module, false);
            changingVar = false;
        }
        if (binary.right instanceof ExprBinary) {
            right = getVarFromBinary((ExprBinary) binary.right, parent, module);
        }
        if (binary.right instanceof ExprBadJoin) {
        	changingVar = binary.op == ExprBinary.Op.IN ? true : false; // If the expression is (Expression in q.var'), then it is possible that a variable (var) is being changed (For parameterized vars)
            right = getVarFromBadJoin((ExprBadJoin) binary.right, parent, module);
            changingVar = false;
        }
        if (binary.right instanceof ExprList) {
        	right = getVarFromExprList((ExprList) binary.right, parent, module, false);
        }
        if (binary.right instanceof ExprConstant) {
        	right = binary.right;
        }
        if (binary.right instanceof ExprList) {
        	right = getVarFromExprList((ExprList) binary.right, parent, module, false);
        }
        if (binary.right instanceof ExprQt) {
        	right = getVarFromExprQt((ExprQt) binary.right, parent, module, new ArrayList<Decl>(), false);
        }
        
        //System.out.println("Right Type: " + right.getClass().getCanonicalName());
        modifyingExprBinary = false;
        return createBinaryExpr(binary.op, left, right);
    }
    
    /*
     * Breakdown a unary expression into its subcomponents Example of an unary
     * expression: one varible
     */
    private static ExprUnary getVarFromUnary(ExprUnary unary, DashConcState parent, DashModule module, boolean inNestedQuant) {
    	Expr sub = null;
    	//System.out.println("Expr Type: " + unary.sub.getClass().getCanonicalName() + " Nested?: " + inNestedQuant);
        if (unary.sub instanceof ExprVar) {
        	modifyingExprUnary = true;
        	changingVar = true;
            sub = modifyExprWithVar(unary.sub, parent, module, false);
            changingVar = false;
            modifyingExprUnary = false;
        }
        if (unary.sub instanceof ExprUnary) {
            sub = getVarFromUnary((ExprUnary) unary.sub, parent, module, inNestedQuant);
        }
        if (unary.sub instanceof ExprBadJoin) {
            sub = getVarFromBadJoin((ExprBadJoin) unary.sub, parent, module);
        }
        if (unary.sub instanceof ExprBinary) {
            sub = getVarFromBinary((ExprBinary) unary.sub, parent, module);
        }
        if (unary.sub instanceof ExprList) {
        	sub = getVarFromExprList((ExprList) unary.sub, parent, module, inNestedQuant);
        }
        if (unary.sub instanceof ExprQt) {
        	sub = getVarFromExprQt((ExprQt) unary.sub, parent, module, new ArrayList<Decl>(), inNestedQuant);
        }
        if (unary.sub instanceof ExprConstant) {
        	sub = unary.sub;
        }

        return createUnaryExpr(unary.op, sub);
    }

    /*
     * Breakdown a Join expression into its subcomponents Example of a join
     * expression: s.variable (jointed by a dot)
     */
    private static ExprBadJoin getVarFromBadJoin(ExprBadJoin joinExpr, DashConcState parent, DashModule module) {
    	Expr left = null, right = null;
        if (joinExpr.left instanceof ExprVar) {
            left = modifyExprWithVar(joinExpr.left, parent, module, false);
        }
        if (joinExpr.left instanceof ExprUnary) {
            left = getVarFromUnary((ExprUnary) joinExpr.left, parent, module, false);
        }
        if (joinExpr.left instanceof ExprBadJoin) {
            left = getVarFromBadJoin((ExprBadJoin) joinExpr.left, parent, module);
        }
        if (joinExpr.left instanceof ExprBinary) {
        	left = getVarFromBinary((ExprBinary) joinExpr.left, parent, module);
        }
        if (joinExpr.left instanceof ExprList) {
        	left = getVarFromExprList((ExprList) joinExpr.left, parent, module, false);
        }
        if (joinExpr.left instanceof ExprConstant) {
        	left = joinExpr.left;
        }
                
        if (joinExpr.right instanceof ExprVar) {
            right = modifyExprWithVar(joinExpr.right, parent, module, false);
        }
        if (joinExpr.right instanceof ExprUnary) {
            right = getVarFromUnary((ExprUnary) joinExpr.right, parent, module, false);
        }
        if (joinExpr.right instanceof ExprBadJoin) {
            right = getVarFromBadJoin((ExprBadJoin) joinExpr.right, parent, module);
        }
        if (joinExpr.right instanceof ExprBinary) {
        	right = getVarFromBinary((ExprBinary) joinExpr.right, parent, module);
        }
        if (joinExpr.right instanceof ExprList) {
        	right = getVarFromExprList((ExprList) joinExpr.right, parent, module, false);
        }
        if (joinExpr.right instanceof ExprConstant) {
        	right = joinExpr.right;
        }  
        
        manageBufferCall(left, right, module, parent);
        
        if (refParamChanged) {
        	if (right instanceof ExprBadJoin && left instanceof ExprBadJoin) {
        		Expr rightRight = ((ExprBadJoin) right).right;
            	//System.out.println("Right: " + right + "RightRight: " + rightRight + " Left: " + left + " Count: " + modifyingExprQT.size());
            	String var = rightRight.toString();
            	if (changedVarByReference.containsKey(var)) {
            		changedVarByReference.get(var).addReference(left);
            	}
            	else {
            		changedVarByReference.put(var, new DashChangedVars(var, parent.isParameterized ? parent.param : null, left));
            	}
            	          	
        		if (modifyingExprQT.size() > 0) {
        			paramVarRefQt.put(rightRight.toString(), left);
        		}
        		else {
        			paramVarRef.put(rightRight.toString(), left);
        		}
        	}
        	refParamChanged = false;
        }

        if (foundBuffer) {
        	right = ExprBadJoin.make(null, null, left, right); //s.
        	left = ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), ExprVar.make(null, ((ExprBadJoin) left).right.toString())); //s_next.bufferName
        }
        if (paramBuffer.size() > 0) {
        	right = ExprBadJoin.make(null, null, left, right); //(pid.s.bufferName).add
        	Expr sNextJoinBuffer = ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), ExprVar.make(null, paramBuffer.keySet().stream().findFirst().get())); //s_next.bufferName
        	left = ExprBadJoin.make(null, null, paramBuffer.get(paramBuffer.keySet().stream().findFirst().get()), sNextJoinBuffer); //(pid.s_next.bufferName)
            paramBuffer.clear();
        }  
                
        return (ExprBadJoin) ExprBadJoin.make(null, null, left, right);
    }
    
    /*
     * Breakdown a list of expressions into its subcomponents
     */
    private static ExprList getVarFromExprList(ExprList list, DashConcState parent, DashModule module, boolean inNestedExprQt) {
    	List<Expr> exprList = new ArrayList<Expr>();
    	for(Expr expr: list.args) {
    		if(expr instanceof ExprQt) {
    			exprList.add(getVarFromExprQt((ExprQt) expr, parent, module, new ArrayList<Decl>(), inNestedExprQt));
    		}
    		if(expr instanceof ExprList) {
    			exprList.add(getVarFromExprList((ExprList) expr, parent, module, inNestedExprQt));
    		}
            if (expr instanceof ExprUnary) {
            	exprList.add(getVarFromUnary((ExprUnary) expr, parent, module, false));
            }
            if (expr instanceof ExprBinary) {
            	exprList.add(getVarFromBinary((ExprBinary) expr, parent, module));
            }
            if (expr instanceof ExprBadJoin) {
            	exprList.add(getVarFromBadJoin((ExprBadJoin) expr, parent, module));
            }
            if (expr instanceof ExprVar) {
            	exprList.add(modifyExprWithVar(expr, parent, module, false));
            }
            if (expr instanceof ExprConstant) {
            	exprList.add(expr);
            }
    	}
    	return createExprList(list.op, exprList);
    }    
    
    /*
     * Breakdown a quantified expression into its subcomponents. An example of a quantified expression is:
     * all p: PID | expression
     */
    private static Expr getVarFromExprQt(ExprQt exprQt, DashConcState parent, DashModule module, List<Decl> args, boolean nestedInExprQt) {
    	Expr subExpr = null;
    	List<Decl> decls = new ArrayList<Decl>();
    	List<Decl> arguments = new ArrayList<>(args);
    	modifyingExprQT.add(exprQt.sub.toString());
    	isCreatingExprQt = true;

    	if (exprQt.op == ExprQt.Op.ONE || exprQt.op == ExprQt.Op.LONE || exprQt.op == ExprQt.Op.SOME) {
        	exprQtDecls.addAll(exprQt.decls);
    		arguments.addAll(exprQt.decls);
    	}
    	
    	System.out.println("Expr: " + exprQt);
        for (Decl decl : exprQt.decls) {
        	System.out.println("Decl: " + decl.expr);
        	if (decl.expr instanceof ExprBinary) {
        		ExprBinary bin = (ExprBinary) decl.expr;
        		System.out.println("Right: " + bin.right + " Type: " + bin.right.getClass().getCanonicalName());
        	}
        }
    	/*
    	if (exprQt.op == ExprQt.Op.ALL && decl.expr instanceof ExprBinary && !(((ExprBinary) decl.expr).right instanceof ExprQt)) { // For the following case: all n: Node - {some Node} | expression [Do not do for set comprehension]
    		System.out.println("Decl Right: " + ((ExprBinary) decl.expr).right);
    		System.out.println("Decl Left: " + ((ExprBinary) decl.expr).left);
    		exprQtDecls.add(decl);
    	}
    	*/
    	
        for (Decl decl : exprQt.decls) {
        	List<ExprVar> a = new ArrayList<ExprVar>();
        	
        	/*
        	if (exprQt.op == ExprQt.Op.ALL && decl.expr instanceof ExprBinary) { // For the following case: all n: Node - {some Node} | expression [Do not do for set comprehension]
        		ExprBinary binary = (ExprBinary) decl.expr;
        		if (binary.right instanceof ExprVar)
        			exprQtDecls.add(decl);
        	}
        	*/
        	
        	for(ExprHasName name: decl.names)
        		a.add(ExprVar.make(null, name.toString()));    
        	Expr b = getVarFromParentExpr(decl.expr, parent, module);       	
        	decls.add(new Decl(null, null, null, null, a, mult(b)));
        }
   
        if (exprQt.sub instanceof ExprQt) {
        	subExpr = getVarFromExprQt((ExprQt) exprQt.sub, parent, module, arguments, true);
        }
        if (exprQt.sub instanceof ExprUnary) {
        	subExpr = getVarFromUnary((ExprUnary) exprQt.sub, parent, module, true);
        }
        if (exprQt.sub instanceof ExprBinary) {
        	subExpr = getVarFromBinary((ExprBinary) exprQt.sub, parent, module);
        }
        if (exprQt.sub instanceof ExprVar) {
        	subExpr = modifyExprWithVar(exprQt.sub, parent, module, true);
        }
        if(exprQt.sub instanceof ExprList) {
        	subExpr = getVarFromExprList((ExprList) exprQt.sub, parent, module, true);
        }
        if(exprQt.sub instanceof ExprBadJoin) {
        	subExpr = getVarFromBadJoin((ExprBadJoin) exprQt.sub, parent, module);
        }
        
        //System.out.println("ExprQt Inner? :" + nestedInExprQt + " Expr: " + exprQt.sub);

        subExpr = constrainChangedQuantifiedVar(subExpr, parent, module);
    	//subExpr = constrainChangedQuantifiedVar(subExpr);
    	changedExprQtVars.clear();
    	exprQtDecls.clear();
        //subExpr = createUnchangedQTVarAST(subExpr, arguments, parent);
        changedQuantifiedVars.clear();
        modifyingExprQT.remove(0);
        paramVarRefQt.clear();
        isCreatingExprQt = false;
        subExpr = createUnchangedQuantifiedBufferAST(module, subExpr, exprQt.op);
        return createExprQt(exprQt.op, decls, subExpr);
    }
    
    /************************* BUFFER FUNCTIONS **************************/
    
    // A buffer call by the user will look as follows: (s.buffer_name).add or (id.s.buffer_Name). If this is the case: we need to modify this expression as follows:
    //(s_next.buffer_name).(s.buffer_name).add or (id.s_next.buffer_name).(id.s.buffer_name).add.since the call to add is: add[buffer, buffer', p]
    // This gets confusing!
    private static void manageBufferCall(Expr left, Expr right, DashModule module, DashConcState parent) {
    	ExprBadJoin joinLeft = null;
        if (left instanceof ExprBadJoin) {
        	 joinLeft = (ExprBadJoin) left;
        	 foundBuffer = (bufferCommands.contains(right.toString()) && module.buffers.containsKey(joinLeft.right.toString())) ? true : false;
        	 if (bufferCommands.contains(right.toString()) && (joinLeft.right instanceof ExprBadJoin && joinLeft.left instanceof ExprVar)) {
        		 ExprBadJoin joinLeftRight = (ExprBadJoin) joinLeft.right;
        		 if (module.buffers.containsKey(joinLeftRight.right.toString()) && bufferCommands.contains(right.toString())) {
        			 //System.out.println("Changing1: " + joinLeftRight.right.toString() + " Left: " + joinLeft.left + " Command: " + right.toString());
        			 paramBuffer.put(joinLeftRight.right.toString(), joinLeft.left);
        			 changedVars.put(joinLeftRight.right.toString(), module.buffers.get(joinLeftRight.right.toString()));
        			 if (module.buffers.get(joinLeftRight.right.toString()).isParameterized) {
        				 paramBufferChanged.put(joinLeftRight.right.toString(), joinLeft.left);
        			 }
        		 }
        	 }
        	 // Handles cases in which a parametererized conc state makes the following call: (p.bufferName).remove [a buffer call with no parameters such as remove]
        	 if (bufferCommands.contains(right.toString()) && (joinLeft.right instanceof ExprBinary && joinLeft.left instanceof ExprVar)) {
        		 ExprBinary joinLeftRight = (ExprBinary) joinLeft.right;
        		 if (module.buffers.containsKey(joinLeftRight.right.toString()) && bufferCommands.contains(right.toString())) {
        			 //System.out.println("ChangingBuffer2: " + joinLeftRight.right.toString() + " Left: " + joinLeft + " Command: " + right.toString());
        			 paramBuffer.put(joinLeftRight.right.toString(), joinLeft.left);
        			 changedVars.put(joinLeftRight.right.toString(), module.buffers.get(joinLeftRight.right.toString()));
        			 if (module.buffers.get(joinLeftRight.right.toString()).isParameterized) {
        				 //localBufferChanged.put(joinLeftRight.right.toString(), ExprVar.make(null, "p"));
        				 localBufferChanged.put(joinLeftRight.right.toString(), joinLeft.left);
        			 }
        		 }
        	 }
        	 // Handles cases in which a parametererized conc state makes the following call: ConcState[buffer1.first]/buffer0.add[pid]
        	 if (bufferCommands.contains(right.toString()) && (joinLeft.right instanceof ExprBadJoin && joinLeft.left instanceof ExprBadJoin)) {
        		 ExprBadJoin joinLeftRight = (ExprBadJoin) joinLeft.right;
        		 if (module.buffers.containsKey(joinLeftRight.right.toString()) && bufferCommands.contains(right.toString())) {
        			 //System.out.println("Changing3: " + joinLeftRight.right.toString() + " Left: " + joinLeft.left + " Command: " + right.toString());
        			 paramBuffer.put(joinLeftRight.right.toString(), joinLeft.left);
        			 changedVars.put(joinLeftRight.right.toString(), module.buffers.get(joinLeftRight.right.toString()));
        			 if (module.buffers.get(joinLeftRight.right.toString()).isParameterized) {
        				 localBufferChanged.put(joinLeftRight.right.toString(), joinLeft.left);
        			 }
        		 }
        	 }
        }
        if (foundBuffer && joinLeft != null) {
        	changedVars.put(joinLeft.right.toString(), parent);
        }
    }
    
    private static Expr createUnchangedQuantifiedBufferAST(DashModule module, Expr subExpr, ExprQt.Op op) { 	
    	if (isCreatingPreCond) {
    		return subExpr;
    	}
    	for (String buffer: paramBufferChanged.keySet()) {
    		if (op == ExprQt.Op.ALL) {
    			continue;
    		}
    		Expr param = ExprBinary.Op.MINUS.make(null, null, ExprVar.make(null, module.buffers.get(buffer).param), paramBufferChanged.get(buffer));
            Expr binaryLeft = ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "quant"), ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), ExprVar.make(null, buffer)));  //quant.(s_next.bufferName)
            Expr binaryRight = ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "quant"), ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, buffer))); //quant.(s.bufferName)
            Expr binaryEquals = ExprBinary.Op.EQUALS.make(null, null, binaryLeft, binaryRight); // quant.(s_next.bufferName) = quant.(s.bufferName)
            
            List<Decl> decls = new ArrayList<Decl>();
            ExprVar q = ExprVar.make(null, "quant");
            List<ExprVar> a = new ArrayList<ExprVar>(Arrays.asList(q)); //[quant]
            decls.add(new Decl(null, null, null, null, a, mult(param))); //quant: param
            Expr expr = ExprQt.Op.ALL.make(null, null, decls, binaryEquals);
            subExpr = ExprBinary.Op.AND.make(null, null, subExpr, expr);
    	}
    	paramBufferChanged.clear();
    	return subExpr;
    }
    
    private static Expr constrainChangedBuffer(String var, DashConcState varParent, Expr ref) {
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        Expr param = ExprBinary.Op.MINUS.make(null, null, ExprVar.make(null, varParent.param), ref); // param - ref
        Expr quant = ExprVar.make(null, "quant");
        a.add((ExprVar) quant);
        decls.add(new Decl(null, null, null, null, a, mult(param))); //quant: param - ref
        

        Expr binaryLeft = ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), ExprVar.make(null, var)); 
        binaryLeft = ExprBadJoin.make(null, null, quant, binaryLeft); //quant.(s_next).var
        Expr binaryRight = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, var)); //quant.(s_next).var
        binaryRight = ExprBadJoin.make(null, null, quant, binaryRight);
        Expr binaryEquals = ExprBinary.Op.EQUALS.make(null, null, binaryLeft, binaryRight);
        
        //System.out.println("Buffer: " + ExprQt.Op.ALL.make(null, null, decls, binaryEquals));
        
        return ExprQt.Op.ALL.make(null, null, decls, binaryEquals); //all quant: Param - Ref | quant.var' = quant.var
    }
    
    /*************************** CREATING COMPLEX EXPRESSION ******************************/
    
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
    
    /*************************** SINGLE STEP FACT FUNCTION ******************************/
    
    /* Create the single input assumption */
    static void createSingleStepFact(DashModule module)
    {
        // Creating the following expression: all s: Snapshot | lone (s.events & EnvironmentEvent)
    	
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        
        Expr snapshot = ExprUnary.Op.ONE.make(null, ExprVar.make(null, "Snapshot"));
        Expr s = ExprVar.make(null, "s");
        Expr expression = null; //This is the final expression to be stored in the Fact AST
        
        /* Creating the following expression: lone (s.events & EnvironmentEvent) */
        Expr rightQT = null;
        Expr join = ExprBadJoin.make(null, null, s, ExprVar.make(null, "events")); // s.events
        Expr rightBinary = ExprBinary.Op.INTERSECT.make(null, null, join, ExprVar.make(null, "EnvironmentEvent")); // s_next.events & InternalEvent
        rightQT = ExprUnary.Op.LONE.make(null, rightBinary); // no (s_next.events & InternalEvent)
        
        /* Creating the following expression: all s: Snapshot | lone (s.events & EnvironmentEvent) */
        a.add((ExprVar) s);
        decls.add(new Decl(null, null, null, null, a, mult(snapshot))); //s: Snapshot
        expression = ExprQt.Op.ALL.make(null, null, new ArrayList<Decl>(decls), rightQT); //all s: Snapshot | lone (s.events & EnvironmentEvent)
        
        module.addFact(null, "", expression);
    }
    
    /*************************** CTL MODULE FACT FUNCION ******************************/
    
    static void createCTLFact(DashModule module) {
    	// Creating the following expression:     
        //	all s, s_next | small_step[s, s_next] => s->s_next = ks_sigma
        //	Step.initial = ks_s0
    	
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        ExprVar s = ExprVar.make(null, "s");
        ExprVar sNext = ExprVar.make(null, "s_next");
        Expr snapshot = ExprVar.make(null, "Snapshot");
        Expr expression = null; //This is the final expression to be stored in the Fact AST
        a.add(s);
        a.add(sNext);
        decls.add(new Decl(null, null, null, null, a, mult(snapshot))); //s, s_next: Snapshot 
        
        Expr smallStepCall = ExprBadJoin.make(null, null, s, ExprVar.make(null, "small_step"));//s_next.small_step
        smallStepCall = ExprBadJoin.make(null, null, sNext, smallStepCall); //s.s_next.small_step
        Expr arrow = ExprBinary.Op.ARROW.make(null, null, s, sNext); // s->s_next
        Expr sSNextInSigma = ExprBinary.Op.IN.make(null, null, arrow, ExprVar.make(null, "ks_sigma")); // s->s_next = ks_sigma
        Expr implesEqualsSigma = ExprBinary.Op.IFF.make(null, null, sSNextInSigma, smallStepCall); // ->s_next = ks_sigma iff small_step[s, s_next]
        expression = ExprQt.Op.ALL.make(null, null, decls, implesEqualsSigma);
        a.clear();
        decls.clear();
        
        /*
         * Creating the following expression: all s: Snapshot | s in ks_s0 iff init[s]
         */
        a.add((ExprVar) s);
        decls.add(new Decl(null, null, null, null, a, mult(snapshot))); //s: Snapshot
        Expr rightQT = ExprBinary.Op.IFF.make(null, null, ExprBinary.Op.IN.make(null, null, s, ExprVar.make(null, "ks_s0")), ExprBadJoin.make(null, null, s, ExprVar.make(null, "init")));
        expression = ExprBinary.Op.AND.make(null, null, ExprQt.Op.ALL.make(null, null, new ArrayList<Decl>(decls), rightQT), expression); //all s: Snapshot | s in ks_s0 iff init[s]
        a.clear();
        decls.clear();
        
        module.addFact(null, "tcmc", expression);
    }
    
    /*************************** SIGNIFICANCE AXIOM FUNCIONS ******************************/
    
    static void createSignificanceAxiomAST(DashModule module)
    {
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        
        Expr snapshot = ExprVar.make(null, "Snapshot");
        Expr s = ExprVar.make(null, "s");
        Expr reachabilityAxiomExpr = null; //This is the Reachability Axiom, all s : Snapshot | s in S .((Step.initial) <: * (Step.next_step) )
        
        Expr next = null;
        Expr initFirst = null;
        if (DashOptions.generateTraces) {
        	next = ExprVar.make(null, "snapshot/next"); //next
        	initFirst = ExprVar.make(null, "snapshot/first"); // ordering/first
        }
        else if(DashOptions.ctlModelChecking) {
        	next = ExprVar.make(null, "ctl/ks_sigma"); //next
        	initFirst = ExprVar.make(null, "ctl/ks_s0"); // ordering/first
        }
        else {
        	ExprVar sInit = ExprVar.make(null, "s_init");
        	Expr initSInit = ExprBadJoin.make(null, null, sInit, ExprVar.make(null, "init")); //s_init.init or init[s_init]
        	next = ExprBinary.Op.JOIN.make(null, null, snapshot, ExprVar.make(null, "next")); //Snapshot.next
        	Expr reflexiveClosure = ExprUnary.Op.RCLOSURE.make(null, next); // * (Snapshot.next)
        	Expr domain = ExprBinary.Op.DOMAIN.make(null, null, sInit, reflexiveClosure); // (s_init <: * (next))
        	Expr joinDomain = ExprBadJoin.make(null, null, snapshot, domain); // Snapshot.(s_init <: * (next))
        	Expr sInDomain = ExprBinary.Op.IN.make(null, null, s, joinDomain); // s in Snapshot.(s_init <: * (next))
        	Expr sInitAndSInDomain = ExprBinary.Op.AND.make(null, null, initSInit, sInDomain); // init[s_init] and s in (s_init <: * (next))
        	a.add(sInit);
        	decls.add(new Decl(null, null, null, null, a, mult(snapshot))); //s_init: Snapshot
        	Expr someQt = ExprQt.Op.SOME.make(null, null, new ArrayList<Decl>(decls), sInitAndSInDomain); // some s: Snapshot | init[s_init] and s in (s_init <: * (next))
        	a.clear();
        	decls.clear();
        	a.add((ExprVar) s);
        	decls.add(new Decl(null, null, null, null, a, mult(snapshot))); //s: Snapshot
        	Expr reachabilityAxiom = ExprQt.Op.ALL.make(null, null, new ArrayList<Decl>(decls), someQt); // all s: Snapshot | some s_init: Snapshot | init[s_init] and s in (s_init <: * (next))
        	addPredicateAST(module, "reachabilityAxiom", null, null, null, null, reachabilityAxiom);
        	return;
        }
     
        Expr reflexiveClosure = ExprUnary.Op.RCLOSURE.make(null, next); // * (next)
        Expr domain = ExprBinary.Op.DOMAIN.make(null, null, initFirst, reflexiveClosure); // (ordering/first <: * (next))
        
        Expr SJoinDomain = ExprBadJoin.make(null, null, snapshot, domain); // Snapshot. (ordering/first <: * (next))
        Expr sInSJoinDomain = ExprBinary.Op.IN.make(null, null, s, SJoinDomain); // s in Snapshot. (ordering/first <: * (next))
        
        a.add((ExprVar) s);
        decls.add(new Decl(null, null, null, null, a, mult(snapshot))); //s: Snapshot
        reachabilityAxiomExpr = ExprQt.Op.ALL.make(null, null, new ArrayList<Decl>(decls), sInSJoinDomain); // all s: Snapshot | s in Snapshot. ((Step.initial) <: * (Step.next_step) )
        addPredicateAST(module, "reachabilityAxiom", null, null, null, null, reachabilityAxiomExpr);
    }
    
    static void createOperationsAxiomAST(DashModule module)
    {
        //This is the Operations Axiom, some s, s_next : S | T[s, s] for every transition T
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        
        Expr snapshot = ExprVar.make(null, "Snapshot");
        Expr s = ExprVar.make(null, "s");
        Expr sNext = ExprVar.make(null, "s_next");
        a.add((ExprVar) s);
        a.add((ExprVar) sNext);
        decls.add(new Decl(null, null, null, null, a, mult(snapshot))); //s, s_next: Snapshot
        
        Expr expression = null;
        for (String transName: module.transitions.keySet())
        {
        	Expr sJoinTrans = ExprBadJoin.make(null, null, s, ExprVar.make(null, transName)); //T[s] or s.T
        	Expr join = ExprBadJoin.make(null, null, sNext, sJoinTrans); // T[s, s_next] or s_next.s.T
        	Expr quantified = ExprQt.Op.SOME.make(null, null, new ArrayList<Decl>(decls), join); // some s, s_next: Snapshot | T[s, s_next]
        	
        	if (expression == null)
        		expression = quantified;
        	else
        		expression = ExprBinary.Op.AND.make(null, null, expression, quantified);
        }
        
        addPredicateAST(module, "operationsAxiom", null, null, null, null, expression);
    }
    
    /*************************** HELPER FUNCTIONS ******************************/
    /*
     * Convert ExprVar expression to ExprUnary
     */
    private static Expr convertToExprUnary(Expr b) {
    	if (b instanceof ExprVar) {
    		return ExprUnary.Op.SETOF.make(null, b);
    	}
    	return b;
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
    
    /* Get all the transitions within a state */
    private static void getInnerTransitions(DashState state, List<DashTrans> transitions) {
    	for(DashTrans trans: state.transitions) {
    		transitions.add(trans);
    	}
    	
    	for(DashState innerState: state.states) {
    		getInnerTransitions(innerState, transitions);
    	}
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
    
    static DashState getState(String stateName, DashModule module) {
    	for(DashState state: module.states.values()) {
    		if(state.modifiedName.equals(stateName))
    			return state;
    	}
    	return null;
    }
    
    /* Get all the transitions declared within a concurrent state */
    private static List<String> getTransitions(DashModule module, DashConcState concState)
    {
    	List<String> transitions = new ArrayList<String>();
    	for (DashTrans trans: module.transitions.values()) {
    		if (getParentConcState(trans.parentState).modifiedName.equals(concState.modifiedName))
    			transitions.add(trans.modifiedName);
    	}
    	return transitions;
    }
    
    /* Get all the states declared within a concurrent state */
    private static List<String> getStates(DashConcState concState)
    {
    	List<String> states = new ArrayList<String>();
    	for (DashState state: concState.states) {
    		states.add(state.modifiedName);
    		states.addAll(getInnerStates(state));
    	}
    	return states;
    }
    
    /* Get all the events declared within a concurrent state */
    private static List<String> getEvents(DashConcState concState)
    {
    	List<String> events = new ArrayList<String>();
    	for (DashEvent event: concState.events) {
    		events.add(event.modifiedName);
    	}
    	return events;
    }
    
    private static List<String> getInnerStates (DashState state)
    {
    	List<String> states = new ArrayList<String>();
    	for (DashState innerState: state.states) {
    		states.add(innerState.modifiedName);
    		if (innerState.states.size() > 0) 
    			states.addAll(getInnerStates(innerState));
    	}
    	return states;
    }
    
    /* Get the parent OR state of an OR state (if it is a child state) */
    private static DashState getParentSourceState(DashTrans trans, DashModule module) {   	
    	DashState sourceState = DashToCoreDash.getStateFromName(trans.fromExpr.fromExpr.get(0), module);
    	
    	if(sourceState == null)
    		return null;
    	
    	/* If a source state is a child of a parent OR state, then we need to transition from that state */
    	while(sourceState.parent instanceof DashState) {  		
    		sourceState = (DashState) (sourceState).parent;
    	}
    	
    	return sourceState;
    }
    
    /*************************** ENTER/EXIT FUNCIONS ******************************/
    
    public static void createEnterPredAST(DashModule module) {
    	Expr expr = null;
    	for(DashState state: module.states.values()) {
    		for(DashEnter enter: state.enter) {
    			expr = getVarFromParentExpr(enter.expr, getParentConcState(state.parent), module);
    			addPredicateAST(module, "enter_" + state.modifiedName, "s", null, null, null, expr);
    		}
    	}
    }
    
    public static void createExitPredAST(DashModule module) {
    	Expr expr = null;
    	for(DashState state: module.states.values()) {
    		for(DashExit exit: state.exit) {
    			expr = getVarFromParentExpr(exit.expr, getParentConcState(state.parent), module);
    			addPredicateAST(module, "exit_" + state.modifiedName, "s", null, null, null, expr);
    		}
    	}
    }
    
    private static Expr createExitAST(Expr expression, DashState sourceState, DashTrans transition) {
        if(transition.fromExpr.fromExpr.size() > 0 && sourceState != null) {        	
        	Expr fromExpr = ExprVar.make(null, sourceState.modifiedName);
        	Expr sConf = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "conf")); //s.conf
        	Expr in = ExprBinary.Op.IN.make(null, null, fromExpr, sConf); //source in s.conf
        	Expr some = ExprUnary.Op.SOME.make(null, ExprBinary.Op.INTERSECT.make(null, null, fromExpr, sConf)); //source & s.conf
        	Expr exitCall = ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), ExprVar.make(null, "exit_" + fromExpr.toString()));
        	
            if(sourceState.states.size() > 0) {
            	for(DashState state: sourceState.states) {
            		if(state.isDefault)
            			expression = createExitAST( expression,  state, transition);
            	}     		
            }
        	
        	if(sourceState.exit.size() > 0 && sourceState.states.size() == 0) {
        		return ExprBinary.Op.AND.make(null, null, expression, ExprBinary.Op.IMPLIES.make(null, null, in, exitCall));
        	}
        	else if(sourceState.exit.size() > 0 && sourceState.states.size() > 0) {
        		return ExprBinary.Op.AND.make(null, null, expression, ExprBinary.Op.IMPLIES.make(null, null, some, exitCall));
        	}
        }
        return expression;
    }
    
    /**************************************** ACTION/CONDITION FUNCTIONS **********************************/
    
    private static Expr replaceWithActionExpr(Expr expr, DashConcState parent, DashModule module) {
        if(expr instanceof ExprVar) {
            for (DashAction value : module.actions.values()) {
                if (expr.toString().equals(value.name))
                	return getVarFromParentExpr(value.expr, parent, module);
            }
        }
        return expr;
    }
    
    private static Expr replaceWithConditionExpr(Expr expr, DashConcState parent, DashModule module) {
        if(expr instanceof ExprVar) {
            for (DashCondition value : parent.condition) {
                if (expr.toString().equals(value.name))
                	return getVarFromParentExpr(value.expr, parent, module);
            }
        }
        return expr;
    }
    
    /***************************** CREATING INVARIANT FACT *******************************/
    
    private static void createInvariantFact(DashModule module) {
    	isCreatingInvariant = true;
    	for(DashInvariant invar: module.invariants.values()) {
    		addInvariantFact(invar, module);
    	}
    	isCreatingInvariant = false;
    }

    private static void addInvariantFact(DashInvariant invar, DashModule module) {
    	Expr expression = null;

    	for(Expr expr: invar.exprList) {
    		if (expression == null)
    			expression = getVarFromParentExpr(expr, getParentConcState(invar.parent), module);
    		else
    			expression = ExprBinary.Op.AND.make(null, null, getVarFromParentExpr(expr, getParentConcState(invar.parent), module), expression);
        }

        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        Expr snapshot =  ExprVar.make(null, "Snapshot");
        a.add(ExprVar.make(null, "s"));
        decls.add(new Decl(null, null, null, null, a, mult(snapshot)));

    	Expr quantifiedExpr = ExprQt.Op.ALL.make(null, null, decls, expression);

    	module.addFact(null, invar.name, quantifiedExpr);
    }
    
    /*************************** COMMAND FUNCIONS ******************************/
    
    private static void convertCommand(DashModule module) {
    	for (int i = 0; i < module.commands.size(); i++) {
    		module.commands.set(i, modifyCommand(module.commands.get(i), module));
    	}
    }
    
    public static Command modifyCommand(Command command, DashModule module){
    	List<CommandScope> scopes = new ArrayList<CommandScope>();
		int paramScope = 2;
		int stateLabelScope = 0;
		int transitionLabelScope = 0;
		
    	for (CommandScope scope: command.scope) {
    		if (module.rawBufferNameToIndex.containsKey(scope.sig.label)) {
	        	CommandScope sigNum = new CommandScope(null            , Sig.NONE, scope.isExact,          scope.endingScope, scope.endingScope,             1    );
	        	CommandScope sigScope = new CommandScope(null, new PrimSig(module.rawBufferNameToIndex.get(scope.sig.label), AttrType.WHERE.make(new Pos(null, 0, 0))), sigNum.isExact, sigNum.startingScope, sigNum.endingScope, sigNum.increment);
	        	scopes.add(sigScope);
    		}
    		else if (module.bufferParamToConcState.containsKey(scope.sig.label)){
    			paramScope = scope.endingScope;
    			stateLabelScope += (paramScope *getStates(module.bufferParamToConcState.get(scope.sig.label)).size());
				transitionLabelScope += (paramScope *getTransitions(module, module.bufferParamToConcState.get(scope.sig.label)).size());
				
	        	CommandScope sigNum = new CommandScope(null            , Sig.NONE, scope.isExact,          scope.endingScope, scope.endingScope,             1    );
	        	CommandScope sigScope = new CommandScope(null, new PrimSig(scope.sig.label, AttrType.WHERE.make(new Pos(null, 0, 0))), sigNum.isExact, sigNum.startingScope, sigNum.endingScope, sigNum.increment);
	        	scopes.add(sigScope);    			
    		}
    		else {
	        	CommandScope sigNum = new CommandScope(null            , Sig.NONE, scope.isExact,          scope.endingScope, scope.endingScope,             1    );
	        	CommandScope sigScope = new CommandScope(null, new PrimSig(scope.sig.label, AttrType.WHERE.make(new Pos(null, 0, 0))), sigNum.isExact, sigNum.startingScope, sigNum.endingScope, sigNum.increment);
	        	scopes.add(sigScope);  
    		}
    	}
    	
		for (DashConcState concState: module.concStates.values()) {
			if (!concState.isParameterized) {
				stateLabelScope += getStates(concState).size();
				transitionLabelScope += getTransitions(module, concState).size();
			}
		}
		
		CommandScope stateNumber = new CommandScope(null            , Sig.NONE, false,          stateLabelScope, stateLabelScope,             1    );
		CommandScope stateSigScope = new CommandScope(null, new PrimSig("StateLabel", AttrType.WHERE.make(new Pos(null, 0, 0))), stateNumber.isExact, stateNumber.startingScope, stateNumber.endingScope, stateNumber.increment);
		scopes.add(stateSigScope);
		
		CommandScope transitionNumber = new CommandScope(null            , Sig.NONE, false,          transitionLabelScope, transitionLabelScope,             1    );
		CommandScope transitionSigScope = new CommandScope(null, new PrimSig("TransitionLabel", AttrType.WHERE.make(new Pos(null, 0, 0))), transitionNumber.isExact, transitionNumber.startingScope, transitionNumber.endingScope, transitionNumber.increment);
		scopes.add(transitionSigScope);
        
        int eventLabelScope = 0;
        if(DashOptions.isEnvEventModel) {
        	eventLabelScope = 4;
        }
        
		CommandScope number = new CommandScope(null            , Sig.NONE, false,          eventLabelScope, eventLabelScope,             1    );
		CommandScope sigScope = new CommandScope(null, new PrimSig("EventLabel", AttrType.WHERE.make(new Pos(null, 0, 0))), number.isExact, number.startingScope, number.endingScope, number.increment);
		scopes.add(sigScope);
		
		return command.check ? createCommand(false,ExprVar.make(null, "c"), null , ExprVar.make(null, command.label) ,null, scopes, null, module) : createCommand(false,ExprVar.make(null, "r"), null , ExprVar.make(null, command.label) ,null, scopes, null, module);
    }
    
    
    //Taken from the Dash.cup file for adding in commands
    private static Command createCommand(boolean follow, ExprVar o, ExprVar x, ExprVar n, Expr e, List<CommandScope> s, ExprConstant c, DashModule module) throws Err {
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
        return addCommand(follow, null, n, o.label.equals("c"), overall, bitwidth, maxseq, mintime, maxtime, expects, s, x, module);
    }

	/** Add a COMMAND declaration. */
    public static Command addCommand(boolean followUp, Pos pos, ExprVar name, boolean check, int overall, int bitwidth, int seq, int tmn, int tmx, int exp, List<CommandScope> scopes, ExprVar label, DashModule module) throws Err {
        if (followUp && !Version.experimental)
            throw new ErrorSyntax(pos, "Syntax error encountering => symbol.");
        if (label != null)
            pos = Pos.UNKNOWN.merge(pos).merge(label.pos);
        if (name.label.length() == 0)
            throw new ErrorSyntax(pos, "Predicate/assertion name cannot be empty.");
        if (name.label.indexOf('@') >= 0)
            throw new ErrorSyntax(pos, "Predicate/assertion name cannot contain \'@\'");
        String labelName = (label == null || label.label.length() == 0) ? name.label : label.label;
        Command parent = followUp ? module.commands.get(module.commands.size() - 1) : null;
        Command newcommand = new Command(pos, name, labelName, check, overall, bitwidth, seq, tmn, tmx, exp, scopes, null, name, parent);
        return newcommand;
    }
}