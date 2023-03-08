package ca.uwaterloo.watform.ast;

//tmp
import java.util.*;

import java.util.List;
import java.util.ArrayList;
import java.util.StringJoiner;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;

import ca.uwaterloo.watform.core.DashStrings;

public class DashState  extends Dash {

	// stuff from parsing
	private String name;
	private String param; 
	private DashStrings.StateKind kind; // basic state = OR with no subStates
	private DashStrings.DefKind def; 
	private List<Object> items;
	private int tabsize = 2;

	// fully general constructor
	// 6 args
	public DashState(Pos p, String n, String prm, DashStrings.StateKind k, DashStrings.DefKind d, List<Object> i) {
		this.pos = p;
		this.name = n;
		this.param = prm;
		this.kind = k;
		this.def = d;
		this.items = i;
	
	}
	// basic state - default or non-default
	// 3 args
	public DashState(Pos p, String n, DashStrings.DefKind d) {
		this.pos = p;
		this.name = n;
		this.param = null;
		this.kind = DashStrings.StateKind.BASIC;
		this.def = d;
		this.items = null;
	}
	// and/or state; non-parameterized
	// 5 args
	public DashState(Pos p, String n, DashStrings.StateKind k, DashStrings.DefKind d, List<Object> i) {
		this.pos = p;
		this.name = n;
		this.param = null;
		this.kind = DashStrings.StateKind.OR;
		this.def = d;
		this.items = i;	
	}
	// and state; parameterized
	// 4 args
	public DashState(Pos p, String n, String prm, List<Object> i) {
		assert(p != null);
		this.pos = p;
		this.name = n;
		this.param = prm;
		this.kind = DashStrings.StateKind.AND;
		this.def = DashStrings.DefKind.NOTDEFAULT;
		this.items = i;	
	}

	public String toString() {
		String s = new String("");
		//s += s.join("", Collections.nCopies(tab*tabsize, " "));
		if (def == DashStrings.DefKind.DEFAULT) {
			s += DashStrings.defaultName + " ";
		}
		if (kind == DashStrings.StateKind.AND) {
			s += DashStrings.concName +" ";
		}
		if (items == null) {
			s += DashStrings.stateName + " " + name + " { }\n";
		} else { 
		    s += DashStrings.stateName + " " + name;
			if (param == null) s += " {\n";
			else s += " [" + param + "] {\n";
			StringJoiner j = new StringJoiner("");
 			items.forEach(i -> j.add(i.toString()));
			s += j.toString() + "}\n";

		}
		return s;
	}

	/*
	public String getParam() {
		return params(1)
	}
	public String getParams() {
		return params;
	}
	public String getFullyQualName() {
		return pathHere+"/"+name;
	}

	public getAllTransitions() {
		returns allTransitions;
	}

	public getAllEvents() {
		return allEvents;
	}

	public getAllParams() {
		return allParams;
	}


	// correctness checks 
	public boolean allSubStatesSameKind() {
		if (subStates != null) {
			StateKind k = substates(1).getKind();
			for (s:subStates) {
				if (k != s.getKind()) {
					error
				}
			}
			return true;
		} else {
			return false;
		}
	}

	public getDefaultBasicStates() {
		switch (kind):
			case StateKind.BASIC:
				return getFullyQualifiedName()
			case StateKind.OR:
				return getDefaultState


			} else if (kind == StateKind.OR) {

			} else {
				// error 
			}
		}
	}
	public void resolveVars(String pth, List<StringList> prs) {
		for (d:dynvars) {
			d.setPathToHere(pth);
			d.setParams(params)
		}
	}

	public void resolveEvents(String pth) {
		for (e:events) {
			e.setPathToHere(pth);
		}
	}
	public void resolveTrans(String pth, List<StringList> prs) {
		for (t:transitions) {
			t.setPathToHere(pth);
			t.setParems(params);
			// calculate scope to put in table
			// reject transition as crossing from one concurrent component to another if children of scope are concurrent !!		
		}
		// what if no transitions
	}

			// 1) all sibling states must be same type

		// env events cannot be generated
		// env vars cannot be primed anywhere
		// must have at least one transition (could be looping on Root ...)
	
	public void resolveAll(String pth, List<String> prs, String parent) {
		List<String> params = prs.add(prm);
		st.add(fulQualName(pth,name),params,parent, children)

		if (isBasicState()) {
			allTransitions = new ArrayList();
			symbolTable = ??;
			allEvents = new ArrayList();			
			stateTable.add(s, {s}, {s})
			return;
		} else {
			allSubStatesSameKind()
			// set the pathtohere and params of variables 
			// set the FQNs of src and dest of transitions
			resolveVars(pth,prs);
			resolveEvents(pth);
			resolveTrans(pth,prs);
			String defName = null;
			for (s:substates) {
				s.resolveAll(pathToHere, params);
				// collect all the stuff from below
				// set trans src/dest FQNs
				allTransitions.addAll(s.getAllTransitions());
				symbolTable.addAll(s.getSymbolTable());
				allEvents.addAll(s.getAllEvents());
				allParams.addAll(s.getAllParams());
				// calculate all basic states entered/exited and pass up?
				// or do that in StateTableResolve all??
				if (s.kind == StateKind.OR) {
					if (defName == null) {
						defName = s.getFullyQualName();
					} else {
						// error multiple default states
					}
				} else {
					defN
				}
				stateTable.merge(s.getStateTable());
				// what about parameters of states???
			}
			stateTable.add(s,)
		}
		isResolved = true;
	}
	*/
}