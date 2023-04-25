package ca.uwaterloo.watform.ast;

import java.util.*;

import java.util.List;
import java.util.ArrayList;
import java.util.StringJoiner;
import java.util.Collections;
import java.util.stream.Collectors;


import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;

import ca.uwaterloo.watform.core.*;

import ca.uwaterloo.watform.alloyasthelper.ExprHelper;
import ca.uwaterloo.watform.parser.StateTable;
import ca.uwaterloo.watform.parser.TransTable;
import ca.uwaterloo.watform.parser.EventTable;
import ca.uwaterloo.watform.parser.VarTable;
import ca.uwaterloo.watform.parser.BufferTable;

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
		assert(n != null && i != null);
		this.pos = p;
		this.name = n;
		this.param = prm;
		this.kind = k;
		this.def = d;
		this.items = i;
		//System.out.println("here1 creating "+this.name);
		//System.out.println("here1 " + (this.param == null));
	
	}
	/*
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
	*/
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

	public static String noParam() {
		return null;
	}
	public static List<Object> noSubstates() {
		return new ArrayList<Object>();
	}
		// env events cannot be generated
		// env vars cannot be primed anywhere
		// must have at least one transition (could be looping on Root ...)
	
	/*
	 * check for errors in the state hierarchy
	 * and put all states in the state table
	 * also set this state's fqn here
	 */
	public void resolveAllStates(StateTable st, EventTable et, VarTable vt, BufferTable bt, List<String> params, List<String> ances)  {
		if (DashFQN.alreadyFQN(name)) DashErrors.stateNameCantBeFQN(pos, name);
		sfqn = DashFQN.fqn(ances,name);
		//System.out.println("Resolving state "+sfqn);
	
		// process the children
		// have to make a copy so that recursion does not just
		// continue to add to list everywhere				
		List<String> newAnces = new ArrayList<String>(ances);
		newAnces.add(name);		
		List<String> newParams = new ArrayList<String>(params);
		if (param != null) newParams.add(param);

		List<DashState> substatesList = new ArrayList<DashState>();
		if (items != null)
			substatesList = 
				items.stream()
				.filter(i -> i instanceof DashState)
				.map(p -> (DashState) p)
				.collect(Collectors.toList());

		if (substatesList.isEmpty() ) {

			st.add(sfqn, kind, param, newParams, def, DashFQN.fqn(ances), null);
			
		} else {
			
			// all sibling states must have different names
			ArrayList<String> childFQNs = new ArrayList();
			substatesList.forEach(i -> childFQNs.add(DashFQN.fqn(ances,name, i.name)));
			// DashUtilFcns.myprint("childFQNS: "+childFQNs);
			Set<String> dups = DashUtilFcns.findDuplicates(childFQNs);
			if (!dups.isEmpty()) 
				DashErrors.dupSiblingNames(DashUtilFcns.strCommaList(dups.stream().collect(Collectors.toList())));

			// add this state to the table
			st.add(sfqn,kind, param, newParams,def, DashFQN.fqn(ances), childFQNs);

			// add all substates to the table
			for (DashState s: substatesList) s.resolveAllStates(st, et, vt, bt, newParams, newAnces);

			// make sure defaults are correct
			// if there's only one child it is automatically the default
			if (substatesList.size() == 1) {
				// make sure it is set as default
				// this child should already be in the state table
				// might already be set as duplicate but that's okay
				// have to use the substate's FQN here
				st.setAsDefault(childFQNs.get(0));
			} else {
				// default states
				List<DashState> defaultsList = 
					substatesList.stream()
					.filter(i -> (i.def == DashStrings.DefKind.DEFAULT))
					.collect(Collectors.toList());
				List<DashState> andList = 
					substatesList.stream()
					.filter(i -> (i.kind == DashStrings.StateKind.AND))
					.collect(Collectors.toList());
				if (andList.equals(substatesList) && defaultsList.size() == 0) {
					// all AND-states are not designated as defaults so all are defaults
					for (String ch: childFQNs) st.setAsDefault(ch);
				} else if (defaultsList.size() == 0) 
					DashErrors.noDefaultState(sfqn);
				else {
					// if defaults list contains an OR states, it should be size 1
					boolean flag = defaultsList.stream().anyMatch( (s) -> s.kind == DashStrings.StateKind.OR);
					if (flag) {
						if (defaultsList.size() != 1) DashErrors.tooManyDefaults(sfqn);	
						// o/w one OR state is default
					} else {					
						// if defaults list is all c's, all c children should be included
						//System.out.println("defaultsList: "+defaultsList);
						//System.out.println("andList: "+andList);
						if (!(defaultsList.equals(andList))) DashErrors.allAndDefaults(sfqn);
					}
				}
			}
		}

		// add declared events
		List <DashEventDecls> eventDeclsList = new ArrayList<DashEventDecls>();
		if (items != null)
			eventDeclsList = 
				items.stream()
				.filter(i -> i instanceof DashEventDecls)
				.map(p -> (DashEventDecls) p)
				.collect(Collectors.toList());
		// put in event table with FQN 
		for (DashEventDecls e:eventDeclsList) {
			DashStrings.IntEnvKind k = e.getKind();
			for (String x: e.getNames()) {
				if (DashFQN.alreadyFQN(x)) DashErrors.eventNameCantBeFQN(e.getPos(), x);
				String xfqn = DashFQN.fqn(sfqn,x);
				if (!et.add(xfqn,k, newParams)) DashErrors.duplicateEventName(e.getPos(),x);
			}
		}

		// add declared variables
		List <DashVarDecls> varDeclsList = new ArrayList<DashVarDecls>();
		if (items != null)
			varDeclsList = 
				items.stream()
				.filter(i -> i instanceof DashVarDecls)
				.map(p -> (DashVarDecls) p)
				.collect(Collectors.toList());
		// put in var table with FQN 
		for (DashVarDecls v:varDeclsList) {
			DashStrings.IntEnvKind k = v.getKind();
			Expr t = v.getTyp();
			for (String x: v.getNames()) {
				if (DashFQN.alreadyFQN(x)) DashErrors.varNameCantBeFQN(v.getPos(), x);
				String xfqn = DashFQN.fqn(sfqn,x);
				if (!vt.add(xfqn,k, newParams, t)) DashErrors.duplicateVarName(v.getPos(),x);
			}
		}

		// add declared buffers
		List <DashBufferDecls> bufferDeclsList = new ArrayList<DashBufferDecls>();
		if (items != null)
			bufferDeclsList = 
				items.stream()
				.filter(i -> i instanceof DashBufferDecls)
				.map(p -> (DashBufferDecls) p)
				.collect(Collectors.toList());
		// put in var table with FQN 
		for (DashBufferDecls b:bufferDeclsList) {
			DashStrings.IntEnvKind k = b.getKind();
			String el = b.getElement();
			for (String x: b.getNames()) {
				if (DashFQN.alreadyFQN(x)) DashErrors.bufferNameCantBeFQN(b.getPos(), x);
				String xfqn = DashFQN.fqn(sfqn,x);
				if (!bt.add(xfqn,k, newParams, el)) DashErrors.duplicateBufferName(b.getPos(),x);
			}
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

			List<DashRef> fromList = 
				t.items.stream()
				.filter(i -> i instanceof DashFrom)
				.map(p -> ((DashFrom) p).src)
				.collect(Collectors.toList());
			//System.out.println(fromList);
			DashRef src = setSrcDest("from", fromList, st, sfqn, tfqn);
			assert(src != null); 
			st.add(src.getName());  
			
			List<DashRef> gotoList = 
				t.items.stream()
				.filter(i -> i instanceof DashGoto)
				.map(p -> ((DashGoto) p).dest)
				.collect(Collectors.toList());
			//System.out.println(gotoList);
			DashRef dest = setSrcDest("goto", gotoList, st, sfqn, tfqn);
			assert(dest != null); 
			st.add(dest.getName());

			/*
			// AND-cross transitions are now allowed
			// check if it is an AND-cross transition
			List<String> srcAnces = st.getAllAnces(src);
			// System.out.println("src="+src+" srcAnces= "+srcAnces);
			List<String> destAnces = st.getAllAnces(dest);
			// System.out.println("dest="+dest+" destAnces= "+destAnces);
			int i = 0;
			// find closest common ances
			while (i< srcAnces.size() && i < destAnces.size() && srcAnces.get(i).equals(destAnces.get(i))) i++;
			// are there any conc states between src/dest and the closest common ances?
			for (int j=i; j < srcAnces.size();j++)
				if (st.isAnd(srcAnces.get(i)))
					DashErrors.andCrossTransition(tfqn);
			for (int j=i; j < destAnces.size(); j++)
				if (st.isAnd(st.getKind(destAnces.get(i))))
					DashErrors.andCrossTransition(tfqn);
			*/

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

		

	}

	/*
	 * this fcn figures out the src/dest of a transition
	 * from its context
	 * if it has no src/dest, the parent state is used
	 * if it is already FQN, it is returned directly
	 * Otherwise, it looks at all uniquely named states up to an ancestor conc state
	 * Requires state table to have been built already
	 */
 
	public DashRef setSrcDest(String xType, List<DashRef> ll,  StateTable st, String parentFQN, String tfqn) {

		//System.out.println("Here");
		//System.out.println(ll);
		if (ll.size() > 1) {
			DashErrors.moreThanOneSrcDest(xType, tfqn);
			return null;
		} else if (ll.isEmpty()) 
			// can be a loop on root
			return new DashRef(parentFQN, ExprHelper.createVarExprList(DashStrings.pName,st.getParams(parentFQN)));
		else {
			// if has slashes, turn to "-"
			DashRef x = ll.get(0);
			//System.out.println("Looking for: " + x);
			if (DashFQN.alreadyFQN(x.getName())) {
				// number of params provided must match number of params needed
				//System.out.println(x.getParamValues().size());
				//System.out.println(st.getParams(x.getName()).size());
				if (x.getParamValues().size() != st.getParams(x.getName()).size()) {
					DashErrors.fqnSrcDestMustHaveRightNumberParams(xType,tfqn);
					return null;
				}
				return x;
			} else {
				// not fully qualified
				// shouldn't have params in DashRef
				// Root could be here but won't have params 
				if (!x.getParamValues().isEmpty()) {
					DashErrors.srcDestCantHaveParam(xType,tfqn);
					return null;
				}
				// Root ends up here
				List<String> matches = new ArrayList<String>();
				//String a = st.getClosestConcAnces(parentFQN);
				//System.out.println("getClosestConcAnces: "+a);
				//List<String> b = st.getAllNonConcStatesWithinThisState(a);
				//System.out.println("getAllNonConcStatesWithinThisState "+b);
				for (String s:st.getRegion(parentFQN)) {
					if (x.getName().equals(DashFQN.chopNameFromFQN(s))) matches.add(s);
				}
				//System.out.println("matches: " + matches);
				if (matches.size() > 1) {
					DashErrors.ambiguousSrcDest(xType, tfqn);
					return null; 
				} else if (matches.isEmpty()) {
					//DashUtilFcns.myprint(st.toString());
					DashErrors.unknownSrcDest(x.getName(),xType,tfqn);
					return null;
				} else {
					String m = matches.get(0);
					//System.out.println(m);
					// must have same param values as trans b/c in same conc region
					return new DashRef(m, paramVars(st.getParams(m)));
				}
			}
		}
	}

    // [n1,n2,...]
    private List<Expr> paramVars(List<String> names) {
        List<Expr> o = new ArrayList<Expr>();
        for (String n: names) o.add(ExprHelper.createVar(DashStrings.pName+n));
        return o;
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