package ca.uwaterloo.watform.rapidDash;

import ca.uwaterloo.watform.ast.DashConcState;
import ca.uwaterloo.watform.ast.DashState;
import ca.uwaterloo.watform.ast.DashTrans;
import ca.uwaterloo.watform.ast.DashInit;
import ca.uwaterloo.watform.ast.DashWhenExpr;
import ca.uwaterloo.watform.parser.DashModule;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprUnary;

import java.util.*;
import java.util.stream.Collectors;

import static edu.mit.csail.sdg.alloy4.TableView.clean;

/**
 * Mutable; this class represents an Dash to Python translation module
 */

public class DashPythonTranslation {

    private DashModule dashModule;

    public List<String> basicSigLabels;

    public List<String> oneSigLabels;

    private Map<String, State> concStateMap;

    /**
     * Constructs a new DashPythonTranslation object
     * @param dashModule - the DashModule we want to translate
     */
    public DashPythonTranslation(DashModule dashModule) {
        this.dashModule = dashModule;

        // get signature names
        this.basicSigLabels = dashModule.sigs.values().stream()
                .filter(this::isSubSig)
                .map(sig -> clean(sig.label))
                .collect(Collectors.toList());

        // get signature names
        this.oneSigLabels = dashModule.sigs.values().stream()
                .filter(this::isOneSig)
                .map(sig -> clean(sig.label))
                .collect(Collectors.toList());

        // get state hierarchy
        this.concStateMap = new HashMap<>();
        // initialize all states instances, TODO: state will have more member variables, here is only used for transitions
        for(String stateName: dashModule.concStates.keySet()){
            this.concStateMap.put(stateName, new State(stateName));
        }
        for(String stateName: dashModule.states.keySet()){
            this.concStateMap.put(stateName, new State(stateName));
        }
        
        
        for(DashConcState state: dashModule.concStates.values()) {
        	// add state variable declarations (decls)
        	for(Decl decl: state.decls) {
        		DashExprToPython dashExprTranslator = new DashExprToPython<>(decl.expr);
        		dashExprTranslator.isDecl = true;
        		this.concStateMap.get(state.modifiedName).addDecl("self." + decl.get() + " = " + dashExprTranslator.toString());
        	}
        	// add state variable initializations and constraints (inits and init_constraints)
        	for(DashInit init: state.init) {
        		for(Expr expr: init.exprList) {
        			// if the Dash init func is empty, there will be one expr that says "true"
        			if(expr.toString().equals("true")) {
        				continue;
        			}
        			DashExprToPython dashExprTranslator = new DashExprToPython<>(expr);
        			// TODO: this (and DashExprToPython) needs to be cleaned up
        			dashExprTranslator.isInit = true;
        			dashExprTranslator.reparseExpr();
        			
        			// if the expression is a constraint on a variable's cardinality, add "assert"
        			// TODO: are other initialization constraint types possible? They need to be handled here
        			if(expr instanceof ExprBinary) {
        				ExprBinary binaryNode = (ExprBinary) expr;
        				if(binaryNode.left instanceof ExprUnary && ((ExprUnary)binaryNode.left).op == ExprUnary.Op.CARDINALITY) {
        					this.concStateMap.get(state.modifiedName).addInitConstraint("assert " + dashExprTranslator.toString());
        					continue;
        				}
        			}
            		this.concStateMap.get(state.modifiedName).addInit(dashExprTranslator.toString());
        		}
        	}
        	
        	// add substates to conc states
        	for(DashConcState substate: state.concStates) {
        		this.concStateMap.get(state.modifiedName).addSubstate(this.concStateMap.get(substate.modifiedName));
        		this.concStateMap.get(substate.modifiedName).parent = concStateMap.get(state.modifiedName);
        	}
        	for(DashState substate: state.states) {
        		this.concStateMap.get(state.modifiedName).addSubstate(this.concStateMap.get(substate.modifiedName));
        		this.concStateMap.get(substate.modifiedName).parent = concStateMap.get(state.modifiedName);
        	}
        }
        
        // add substates to dash states
        for(DashState state: dashModule.states.values()) {
        	System.out.println(state);
        	for(DashState substate: state.states) {
        		this.concStateMap.get(state.modifiedName).addSubstate(this.concStateMap.get(substate.modifiedName));
        		this.concStateMap.get(substate.modifiedName).parent = concStateMap.get(state.modifiedName);
        	}
        }

        // generate transitions
        for(DashTrans dashTrans : dashModule.transitions.values()){
            Transition trans = new Transition(dashTrans);
            this.concStateMap.get(trans.getStateName()).addTransition(trans);
        }
    }

    private Boolean isSubSig(Sig sig) {
        return sig.isSubsig != null & sig.isOne == null & sig.isAbstract == null & sig.isEnum == null &
                sig.isLone == null & sig.isMeta == null & sig.isPrivate == null & sig.isSome == null & sig.isSubset == null &
                sig.isVariable == null;
    }

    private Boolean isOneSig(Sig sig) {
        return sig.isOne != null & sig.isAbstract == null & sig.isEnum == null &
                sig.isLone == null & sig.isMeta == null & sig.isPrivate == null & sig.isSome == null & sig.isSubset == null &
                sig.isVariable == null;
    }

    // return all states that aren't substates (to prevent them from appearing multiple times)
    public List<State> getStates() {
    	List<State> states = new ArrayList<State>();
    	for(State state: concStateMap.values()) {
    		if(state.parent == null) {
    			states.add(state);
    		}
    	}
    	return states;
    }

    public class State{
        private String stateName;                       // state name
        private List<Transition>  transitions;   // store the translated code for transitions
        private List<State> substates;
        private List<String> decls;
        private List<String> inits;
        private List<String> init_constraints;
        public State parent = null;
        public State(String stateName){
            this.stateName = stateName;
            this.transitions = new ArrayList<>();
            this.substates = new ArrayList<State>();
            this.decls = new ArrayList<String>();
            this.inits = new ArrayList<String>();
            this.init_constraints = new ArrayList<String>();
        }
        public void addTransition(Transition transition){
            this.transitions.add(transition);
        }
        public String getName(){return stateName;}
        public List<Transition> getTransitions() {return transitions.stream().collect(Collectors.toList());}
        public List<State> getSubstates() { return substates.stream().collect(Collectors.toList()); }
        public List<String> getDecls() { return decls.stream().collect(Collectors.toList()); }
        public List<String> getInits() { return inits.stream().collect(Collectors.toList()); }
        public List<String> getInitConstraints() { return init_constraints.stream().collect(Collectors.toList()); }
        public void addSubstate(State s) { substates.add(s); }
        public void addDecl(String s) { decls.add(s); }
        public void addInit(String s) { inits.add(s); }
        public void addInitConstraint(String s) { init_constraints.add(s); }
    }

    public class Transition{
        private String stateName;                       // state name

        private String fromStateName;
        private String toStateName;
        private String transName;                       // transition name
        private String action;                          // the logic for this transition to be executed
        private String guardCondition;                  // the guard condition of this transition
        private String eventCondition;
        private String triggerEvent;
        private String transTemplate;

        public Transition(DashTrans dashTrans){
            // set default transition information
            this.transName = dashTrans.name;
            this.stateName = ((DashConcState)dashTrans.parentState).name;   // TODO: not sure if this name is fully qualified
            this.fromStateName = stateName;

            // System.out.println("[Debug]: transition: " + dashTrans.name + ", state name: " + this.stateName);

            // check keywords
            if(dashTrans.fromExpr != null){    // determines which state this transition belongs to
                // set state name
                // TODO: need implementation, currently fromStateName is just the statename, which is ok for now
            }
            if(dashTrans.onExpr != null){      // determines the trigger event
                // TODO: event related
                this.eventCondition = "pass\t# <placeholder for Event>";
            }
            if(dashTrans.whenExpr != null){    // determines the guard_condition (if statement)
                // TODO: need to be able to translate the predicates first
                DashExprToPython dashExprTranslator = new DashExprToPython<>(dashTrans.whenExpr);

                // set condition
                this.guardCondition = dashExprTranslator.toString();
            }
            if(dashTrans.doExpr != null){      // determines the action
                // TODO: need to be able to translate the actions first
                // String predicate = ...;

                // set action
                this.action = "pass\t# <placeholder for Action>";
            }
            if(dashTrans.gotoExpr != null){    // determine the next state
                this.toStateName = dashTrans.gotoExpr.toString();
            }
            if(dashTrans.sendExpr != null){    // determines the event to send
                this.triggerEvent = "pass\t# <placeholder for Triggering event>";
            }
            if(dashTrans.transTemplate != null){   // TODO: don't know what this does
                this.transTemplate = "pass\t# <placeholder for Trans Template>";
            }
        }
        public String getTransName(){return transName;}
        public String getStateName(){return stateName;}
        public String getGuardCondition(){return guardCondition;}
        public String getAction(){return action;}
        public String getEventCondition() {return eventCondition;}
        public String getFromStateName() {return fromStateName;}
        public String getToStateName() {return toStateName;}
        public String getTransTemplate() {return transTemplate;}
        public String getTriggerEvent() {return triggerEvent;}
    }
}