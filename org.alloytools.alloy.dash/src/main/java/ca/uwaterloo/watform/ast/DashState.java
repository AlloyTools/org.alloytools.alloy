package ca.uwaterloo.watform.ast;

//tmp
import java.util.*;

import java.util.List;
import java.util.ArrayList;
import java.util.StringJoiner;
import java.util.Collections;
import java.util.stream.Collectors;


import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;

import ca.uwaterloo.watform.core.*;

import ca.uwaterloo.watform.parser.StateTable;
import ca.uwaterloo.watform.parser.TransTable;

public class DashState  extends Dash {

	// stuff from parsing
	public String name;
	private String sfqn; // set during resolveAllState
	private String param; 
	private DashStrings.StateKind kind; // basic state = OR with no subStates
	private DashStrings.DefKind def; 
	private List<Object> items;
	private int tabsize = 2;

	// fully general constructor
	// 6 args
	// probably not used?
	public DashState(Pos p, String n, String prm, DashStrings.StateKind k, DashStrings.DefKind d, List<Object> i) {
		assert(n != null && prm != null & i != null);
		this.pos = p;
		this.name = n;
		this.param = prm;
		this.kind = k;
		this.def = d;
		this.items = i;
		//System.out.println("here1 creating "+this.name+" "+ this.kind);
	
	}
	// basic state - default or non-default
	// 3 args
	public DashState(Pos p, String n, DashStrings.DefKind d) {
		assert(n != null);
		this.pos = p;
		this.name = n;
		this.param = null;
		this.kind = DashStrings.StateKind.OR;
		this.def = d;
		this.items = null; // no substates here makes it a basic state
		//System.out.println("here2 creating "+this.name+" "+ this.kind);
	}
	// non-parametrized and/or/basic state 
	// 5 args
	public DashState(Pos p, String n, DashStrings.StateKind k, DashStrings.DefKind d, List<Object> i) {
		assert(n != null && i != null);
		this.pos = p;
		this.name = n;
		this.param = null;
		this.kind = k;
		this.def = d;
		this.items = i;	
		//System.out.println("here3 creating "+this.name+" "+ this.kind);
	}
	// parametrized and state (cannot be default state) 
	// 4 args
	public DashState(Pos p, String n, String prm, List<Object> i) {
		assert(n != null && prm != null & i != null);
		this.pos = p;
		this.name = n;
		this.param = prm;
		this.kind = DashStrings.StateKind.AND;
		this.def = DashStrings.DefKind.NOTDEFAULT;
		this.items = i;	
		//System.out.println("here4 creating "+this.name+" "+ this.kind);
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

		// env events cannot be generated
		// env vars cannot be primed anywhere
		// must have at least one transition (could be looping on Root ...)
	
	/*
	 * check for errors in the state hierarchy
	 * and put all states in the state table
	 * also sets this state's fqn here
	 */
	public void resolveAllStates(StateTable st, List<String> params, List<String> ances)  {
		if (DashFQN.alreadyFQN(name)) DashErrors.stateNameCantBeFQN(pos, name);
		sfqn = DashFQN.fqn(ances,name);
		System.out.println("Resolving state "+sfqn);
			
		List<String> newParams = new ArrayList<String>(params);
		if (param != null) newParams.add(param);

		// process the children
		// have to make a copy so that recursion does not just
		// continue to add to list everywhere				
		List<String> newAnces = new ArrayList<String>(ances);
		newAnces.add(name);
		

		List<DashState> substatesList = new ArrayList<DashState>();
		if (items != null)
			substatesList = 
				items.stream()
				.filter(i -> i instanceof DashState)
				.map(p -> (DashState) p)
				.collect(Collectors.toList());

		if (substatesList.isEmpty() ) {
			
			if (kind == DashStrings.StateKind.AND)
				DashErrors.concStateNoChildren(sfqn); 
			else if (param != null) 
				DashErrors.basicStateParam(sfqn);
			else
				st.add(sfqn, kind, params, null, DashFQN.fqn(ances), null);
			
		} else {
			
			// all sibling states must have different names
			ArrayList<String> childFQNs = new ArrayList();
			substatesList.forEach(i -> childFQNs.add(DashFQN.fqn(ances,name, i.name)));
			// DashUtilFcns.myprint("childFQNS: "+childFQNs);
			Set<String> dups = DashUtilFcns.findDuplicates(childFQNs);
			if (!dups.isEmpty()) 
				DashErrors.dupSiblingNames(DashUtilFcns.strCommaList(dups.stream().collect(Collectors.toList())));
							
			// all sibling names must be the same type
			Set<DashStrings.StateKind> k = new HashSet<DashStrings.StateKind>();
			substatesList.forEach(i -> k.add(i.kind));
			if (k.size() != 1)
				DashErrors.siblingsSameKind(sfqn);
			
			// if substates are OR, then must be a default unless there is only one substate
			// parent kind does not matter
			String def = null;
			if (k.contains(DashStrings.StateKind.OR) && substatesList.size() != 1) {
				// names of the default states
				List<String> defaultsList = 
					substatesList.stream()
					.filter(i -> (i.def == DashStrings.DefKind.DEFAULT))
					.map(i -> i.name)
					.collect(Collectors.toList());
				if (defaultsList.size() > 1) DashErrors.tooManyDefaults(sfqn);
				else if (defaultsList.isEmpty()) DashErrors.noDefaultState(sfqn);
				else def = defaultsList.get(0);
			} else if (k.contains(DashStrings.StateKind.OR) && substatesList.size() == 1) {
				def = substatesList.get(0).name;
			}
			st.add(sfqn,kind, newParams,def, DashFQN.fqn(ances), childFQNs);

			for (DashState s: substatesList) s.resolveAllStates(st, newParams, newAnces);
		}

			/*
			
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
			*/
	}

	/*
	 * check for errors and put all the trans that are at this level
	 * in the trans table
	 * must be done after resolveAllState
	 * this fcn does not modify anything in this object
	 */
	public void resolveAllTrans(StateTable st, TransTable tt) {

		if (items == null ) return;
		List<DashTrans> transList = 
			items.stream()
			.filter(i -> i instanceof DashTrans)
			.map(p -> (DashTrans) p)
			.collect(Collectors.toList());
		// all trans must have different names
		ArrayList<String> transFQNs = new ArrayList();
		transList.forEach(i -> transFQNs.add(DashFQN.fqn(sfqn, i.name)));
		Set<String> dups = DashUtilFcns.findDuplicates(transFQNs);
		if (!dups.isEmpty()) 
			DashErrors.dupTransNames(DashUtilFcns.strCommaList(dups.stream().collect(Collectors.toList())));

		for (DashTrans t: transList) {
			String tfqn = DashFQN.fqn(sfqn,t.name);

			// transition src/dest have to be resolved here rather than in DashTrans because
			// this src and dest are contextual

			List<String> fromList = 
				t.items.stream()
				.filter(i -> i instanceof DashFrom)
				.map(p -> ((DashFrom) p).src)
				.collect(Collectors.toList());
			String src = setSrcDest("from", fromList, st, sfqn, tfqn);
			assert(src != null); // should have thrown an exception
			st.add(src);  
			
			List<String> gotoList = 
				t.items.stream()
				.filter(i -> i instanceof DashGoto)
				.map(p -> ((DashGoto) p).dest)
				.collect(Collectors.toList());
			String dest = setSrcDest("goto", gotoList, st, sfqn, tfqn);
			assert(dest != null); // should have thrown an exception
			st.add(dest);

			// note that this is not newAnces; states referenced by t can be siblings to the state
			// that t is within

			// check if it is an AND-cross transition
			List<String> srcAnces = st.getAllAnces(src);
			System.out.println("src="+src+" srcAnces= "+srcAnces);
			List<String> destAnces = st.getAllAnces(dest);
			System.out.println("dest="+dest+" destAnces= "+destAnces);
			int i = 0;
			while (i< srcAnces.size() && i < destAnces.size() && srcAnces.get(i).equals(destAnces.get(i))) i++;
			for (int j=i; j < srcAnces.size();j++)
				if (st.getKind(srcAnces.get(i)) == DashStrings.StateKind.AND)
					DashErrors.andCrossTransition(tfqn);
			for (int j=i; j < destAnces.size(); j++)
				if (st.getKind(destAnces.get(i)) == DashStrings.StateKind.AND)
					DashErrors.andCrossTransition(tfqn);
			tt.add(tfqn,st.getParams(sfqn),src,dest);
		}
		if (items != null ) {
			List<DashState> substatesList = 
				items.stream()
				.filter(i -> i instanceof DashState)
				.map(p -> (DashState) p)
				.collect(Collectors.toList());
			for (DashState s: substatesList) s.resolveAllTrans(st, tt);
		}
		//	t.resolveAll(st, tt, newParams, ances);
		

	}

	/*
	 * this fcn figures out the src/dest of a transition
	 * from its context
	 * if it has no src/dest, the parent state is used
	 * if it is already FQN, it is returned directly
	 * Otherwise, it looks at all uniquely named states up to an ancestor conc state
	 * Requires state table to have been built already
	 */
	public String setSrcDest(String xType, List<String> ll,  StateTable st, String parentFQN, String tfqn) {

		if (ll.size() > 1) {
			DashErrors.moreThanOneSrcDest(xType, tfqn);
			return null;
		} else if (ll.isEmpty()) 
			// could be root
			return sfqn;
		else {
			// if has slashes, turn to "-"
			String xName = ll.get(0);
			if (DashFQN.alreadyFQN(xName)) return xName;
			else {
				List<String> matches = new ArrayList<String>();
				for (String s:st.getAllNonConcStatesWithinThisState(st.getClosestConcAnces(parentFQN))) {
					if (xName.equals(DashFQN.chopNameFromFQN(s))) matches.add(s);
				}
				if (matches.size() > 1) {
					DashErrors.ambiguousSrcDest(xType, tfqn);
					return null; 
				} else if (matches.isEmpty()) {
					//DashUtilFcns.myprint(st.toString());
					DashErrors.unknownSrcDest(xName,xType,tfqn);
					return null;
				} else {
					return matches.get(0);
				}
			}
		}
	}

	/*
	public String getParam() {
		return params(1)
	}
	public String getParams() {
		return params;
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

	*/
}