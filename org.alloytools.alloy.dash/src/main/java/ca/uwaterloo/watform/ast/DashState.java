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
//import ca.uwaterloo.watform.parser.BufferTable;

public class DashState  extends Dash {

	// stuff from parsing
	public String name;
	//private String sfqn; // set during resolveAllState
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
	
	/*
	 * check for errors in the state hierarchy
	 * and put all states in the state table
	 */
	public void resolve(StateTable st, TransTable tt, EventTable et, VarTable vt, List<String> params, List<Integer> paramsIdx, List<String> ances)  {
		if (DashFQN.isFQN(name)) DashErrors.stateNameCantBeFQN(pos, name);
		String sfqn = DashFQN.fqn(ances,name);
		//System.out.println("Resolving state "+sfqn);

		// make a copy of the items list so we can
		// subtract from it for error checking
		// but keep the original items for printing, etc.
		List<Object> xItems = new ArrayList<Object>(items);


		// invariants ---------------------
		List <DashInv> invList = new ArrayList<DashInv>();
		if (items != null)
			invList = 
				items.stream()
				.filter(i -> i instanceof DashInv)
				.map(p -> (DashInv) p)
				.collect(Collectors.toList());
		xItems.removeAll(invList);

		// inits ---------------------
		List <DashInit> initList = new ArrayList<DashInit>();
		if (items != null)
			initList = 
				items.stream()
				.filter(i -> i instanceof DashInit)
				.map(p -> (DashInit) p)
				.collect(Collectors.toList());
		xItems.removeAll(initList);

		// actions ---------------------
		List <DashAction> actionList = new ArrayList<DashAction>();
		if (items != null)
			actionList = 
				items.stream()
				.filter(i -> i instanceof DashAction)
				.map(p -> (DashAction) p)
				.collect(Collectors.toList());
		xItems.removeAll(actionList);

		// conditions ---------------------
		List <DashCondition> conditionList = new ArrayList<DashCondition>();
		if (items != null)
			conditionList = 
				items.stream()
				.filter(i -> i instanceof DashCondition)
				.map(p -> (DashCondition) p)
				.collect(Collectors.toList());
		xItems.removeAll(conditionList);

		// ---------------------
		// process the children
		// have to make a copy so that recursion does not just
		// continue to add to list everywhere				
		List<String> newAnces = new ArrayList<String>(ances);
		newAnces.add(name);		
		List<String> newParams = new ArrayList<String>(params);
		List<Integer> newParamsIdx = new ArrayList<Integer>(paramsIdx);
		if (param != null) {
			newParams.add(param);
			int idx = st.addToParamsList(param);
			newParamsIdx.add(idx);
		}

		List<DashState> substatesList = new ArrayList<DashState>();
		if (items != null)
			substatesList = 
				xItems.stream()
				.filter(i -> i instanceof DashState)
				.map(p -> (DashState) p)
				.collect(Collectors.toList());



		if (substatesList.isEmpty() ) {
			if (!st.add(sfqn, kind, param, newParams, newParamsIdx, def, DashFQN.fqn(ances), new ArrayList<String>(),
				invList, initList, actionList, conditionList)) DashErrors.addStateToStateTableDup(sfqn);;
			
		} else {
			
			// all sibling states must have different names
			ArrayList<String> childFQNs = new ArrayList();
			substatesList.forEach(i -> childFQNs.add(DashFQN.fqn(ances,name, i.name)));
			// DashUtilFcns.myprint("childFQNS: "+childFQNs);
			Set<String> dups = DashUtilFcns.findDuplicates(childFQNs);
			if (!dups.isEmpty()) 
				DashErrors.dupSiblingNames(DashUtilFcns.strCommaList(dups.stream().collect(Collectors.toList())));

			// add this state to the table
			if (!st.add(sfqn,kind, param, newParams,newParamsIdx, def, DashFQN.fqn(ances), childFQNs,
				invList, initList, actionList, conditionList)) DashErrors.addStateToStateTableDup(sfqn);;

			// add all substates to the table
			for (DashState s: substatesList) s.resolve(st, tt, et, vt, newParams, newParamsIdx, newAnces);

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
		xItems.removeAll(substatesList);
		
		// add declared events ---------------------
		List <DashEventDecls> eventDeclsList = new ArrayList<DashEventDecls>();
		if (items != null)
			eventDeclsList = 
				xItems.stream()
				.filter(i -> i instanceof DashEventDecls)
				.map(p -> (DashEventDecls) p)
				.collect(Collectors.toList());
		// put in event table with FQN 
		for (DashEventDecls e:eventDeclsList) {
			DashStrings.IntEnvKind k = e.getKind();
			for (String x: e.getNames()) {
				if (DashFQN.isFQN(x)) DashErrors.eventNameCantBeFQN(e.getPos(), x);
				String xfqn = DashFQN.fqn(sfqn,x);
				if (!et.add(xfqn,k, newParams, newParamsIdx)) DashErrors.duplicateEventName(e.getPos(),x);
			}
		}
		xItems.removeAll(eventDeclsList);

		// add declared variables ------------------------
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
				if (DashFQN.isFQN(x)) DashErrors.varNameCantBeFQN(v.getPos(), x);
				String xfqn = DashFQN.fqn(sfqn,x);
				if (!vt.addVar(xfqn,k, newParams, newParamsIdx, t)) DashErrors.duplicateVarName(v.getPos(),x);
			}
		}
		xItems.removeAll(varDeclsList);

		// add declared buffers ---------------------------
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
			Integer idx = b.getStartIndex();
			for (String x: b.getNames()) {
				if (DashFQN.isFQN(x)) DashErrors.bufferNameCantBeFQN(b.getPos(), x);
				String xfqn = DashFQN.fqn(sfqn,x);
				if (!vt.addBuffer(xfqn,k, newParams, newParamsIdx, el, idx)) DashErrors.duplicateBufferName(b.getPos(),x);
				idx++;
			}
			if (idx != b.getEndIndex()+1) DashErrors.bufferIndexDoesNotMatchBufferNumber();
		}
		xItems.removeAll(bufferDeclsList);

		// add transitions ----------------------
		List <DashTrans> transList = new ArrayList<DashTrans>();
		if (items != null)
			transList = 
				items.stream()
				.filter(i -> i instanceof DashTrans)
				.map(p -> (DashTrans) p)
				.collect(Collectors.toList());
		for (DashTrans t:transList) {
			//System.out.println("newAnces: " +newAnces);
			t.resolve(tt, newParams, newParamsIdx, newAnces);
		}
		xItems.removeAll(transList);


		if (!xItems.isEmpty()) DashErrors.nonEmptyStateItems();
	}


}