package ca.uwaterloo.watform.parser;

import java.util.Set;
import java.util.List;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Collections;
import java.util.stream.Collectors;


import edu.mit.csail.sdg.ast.*;
import edu.mit.csail.sdg.alloy4.ConstList;

import static ca.uwaterloo.watform.alloyasthelper.ExprHelper.*;

import ca.uwaterloo.watform.core.*;
import static ca.uwaterloo.watform.core.DashUtilFcns.*;
import static ca.uwaterloo.watform.core.DashStrings.*;
import ca.uwaterloo.watform.core.DashRef;
import ca.uwaterloo.watform.dashtoalloy.Common;

import ca.uwaterloo.watform.parser.StateTable;
import ca.uwaterloo.watform.parser.EventTable;

public class VarTable {

	// stores Var, Buffer Decls in a HashMap based on the event FQN

	// LinkedHashMap so order of keySet is consistent
	// Alloy requires declaration before use for variables
	private LinkedHashMap<String,VarElement> varTable;
	private LinkedHashMap<String,BufferElement> bufferTable;

	public VarTable() {
		this.varTable = new LinkedHashMap<String,VarElement>();
		this.bufferTable = new LinkedHashMap<String,BufferElement>();
	}

	public class VarElement {
		private IntEnvKind kind;
		private List<String> params;
		private List<Integer> paramsIdx;
		private Expr typ;

		public VarElement(
			IntEnvKind k,
			List<String> prms,
			List<Integer> prmsIdx,
			Expr t) {
			assert(prms != null);
			this.kind = k;
			this.params = prms;
			this.paramsIdx = prmsIdx;
			this.typ = t;
		}
		public String toString() {
			String s = new String();
			s += "kind: "+kind+"\n";
			s += "params: "+ NoneStringIfNeeded(params) +"\n";
			s += "paramsIdx: "+ NoneStringIfNeeded(paramsIdx) +"\n";
			s += "typ: "+typ.toString() + "\n";
			return s;
		}
		public void setType(Expr typ) {
			this.typ = typ;
		}
	}

	public void setVarType(String vfqn, Expr typ) {
		if (varTable.containsKey(vfqn)) varTable.get(vfqn).setType(typ);
		else { DashErrors.doesNotExist("setVarType", vfqn); }
	}
	public String toString() {
		String s = new String("VAR TABLE\n");
		for (String k:varTable.keySet()) {
			s += " ----- \n";
			s += k + "\n";
			s += varTable.get(k).toString();
		}
		s += "\nBUFFER TABLE\n";
		for (String k:bufferTable.keySet()) {
			s += " ----- \n";
			s += k + "\n";
			s += bufferTable.get(k).toString();
		}
		return s;
	}	
	public Boolean addVar(String vfqn, IntEnvKind k, List<String> prms, List<Integer> prmsIdx, Expr t) {
		assert(prms!=null);
		if (varTable.containsKey(vfqn)) return false;
		if (hasPrime(vfqn)) { DashErrors.nameShouldNotBePrimed(vfqn); return false; }
		else { varTable.put(vfqn, new VarElement(k,prms, prmsIdx, t)); return true; }
	}

	public void resolve(StateTable st, EventTable et) {

		for (String vfqn: varTable.keySet()) {
			String sfqn = DashFQN.chopPrefixFromFQN(vfqn);
			setVarType(vfqn,ResolveExpr.resolveExpr(st, et, this, "var", false, false, true, sfqn,getVarType(vfqn) ));
		}
		/* TODO: buffer types don't need resolving???? buf[element]
		for (String bfqn: bufferTable.keySet()) {
			String sfqn = DashFQN.chopPrefixFromFQN(bfqn);
			vt.setVarType(vfqn,resolveExpr(null, null, this, "var", false, false, true, sfqn,vt.getVarType(bfqn) ));
		}
		*/

	}
	
	public List<String> getAllVarNames() {
		return new ArrayList<String>(varTable.keySet());
	}
	public List<String> getAllNames() {
		// vars plus buffers
		List<String> x = getAllVarNames();
		x.addAll(getAllBufferNames());
		return x;
	}
	public List<String> getVarsOfState(String sfqn) {
		// return all events declared in this state
		// will have the sfqn as a prefix
		return varTable.keySet().stream()
			// prefix of vfqn are state names
			.filter(i -> DashFQN.chopPrefixFromFQN(i).equals(sfqn))
			.collect(Collectors.toList());	
	}
	public List<String> getBuffersOfState(String sfqn) {
		// return all events declared in this state
		// will have the sfqn as a prefix
		return bufferTable.keySet().stream()
			// prefix of vfqn are state names
			.filter(i -> DashFQN.chopPrefixFromFQN(i).equals(sfqn))
			.collect(Collectors.toList());	
	}
	public List<String> getNamesOfState(String sfqn) {
		List<String> x = getVarsOfState(sfqn);
		x.addAll(getBuffersOfState(sfqn));
		return x;		
	}
	// same function for buffers and variables
	//TODO: what if var and buffer have the same name!!!
	public List<String> getParams(String fqn) {
		//System.out.println("getParams: " + fqn);
		if (bufferTable.containsKey(fqn)) return bufferTable.get(fqn).params;
		if (varTable.containsKey(fqn)) return varTable.get(fqn).params;
		else { DashErrors.varBufferDoesNotExist("getParams", fqn); return null; }
	}
	public List<Integer> getParamsIdx(String fqn) {
		if (bufferTable.containsKey(fqn)) return bufferTable.get(fqn).paramsIdx;
		if (varTable.containsKey(fqn)) return varTable.get(fqn).paramsIdx;
		else { DashErrors.varBufferDoesNotExist("getParams", fqn); return null; }
	}
	public Expr getVarType(String vfqn) {
		if (varTable.containsKey(vfqn)) return varTable.get(vfqn).typ;
		else { DashErrors.varDoesNotExist("getType", vfqn); return null; }
	}
	// same function for buffers and variables
	public boolean isInternal(String fqn) {
		if (bufferTable.containsKey(fqn)) return (bufferTable.get(fqn).kind == IntEnvKind.INT);
		if (varTable.containsKey(fqn)) return (varTable.get(fqn).kind == IntEnvKind.INT);
		else { DashErrors.varBufferDoesNotExist("isInternal", fqn); return false; }
	}

	public class BufferElement {
		private IntEnvKind kind;
		private List<String> params;
		private List<Integer> paramsIdx;
		private String element;
		private Integer index;

		public BufferElement(
			IntEnvKind k,
			List<String> prms,
			List<Integer> prmsIdx,
			String e,
			Integer idx) {
			assert(prms != null);
			this.kind = k;
			this.params = prms;
			this.paramsIdx = prmsIdx;
			this.element = e;
			this.index = idx;
		}
		public String toString() {
			String s = new String();
			s += "kind: "+kind+"\n";
			s += "params: "+ NoneStringIfNeeded(params) +"\n";
			s += "paramsIdx: "+ NoneStringIfNeeded(paramsIdx) +"\n";
			s += "element: "+element.toString() + "\n";
			s += "index:" + index;
			return s;
		}
	}

	public List<String> getAllBufferNames() {
		return new ArrayList<String>(bufferTable.keySet());
	}
	public List<Integer> getBufferIndices() {
		List<Integer> k = new ArrayList();
		for (int i=0; i< getAllBufferNames().size();i++) k.add(i);
		return k;
	}

	public int getBufferIndex(String bfqn) {
		if (bufferTable.containsKey(bfqn)) return bufferTable.get(bfqn).index;
		else { DashErrors.bufferDoesNotExist("getIndex", bfqn); return -1; }
	}
	public String getBufferElement(String bfqn) {
		if (bufferTable.containsKey(bfqn)) return bufferTable.get(bfqn).element;
		else { DashErrors.bufferDoesNotExist("getElement", bfqn); return null; }
	}

	public Boolean addBuffer(String vfqn, IntEnvKind k, List<String> prms, List<Integer> prmsIdx, String el, Integer idx) {
		assert(prms!=null);
		if (bufferTable.containsKey(vfqn)) return false;
		else { bufferTable.put(vfqn, new BufferElement(k,prms, prmsIdx, el, idx)); return true; }
	}


	/*
		results in an Expr for the action that has all references to variables as DashRefExpr's
		fqn is a parameter to determine transition parameters and for error messages
		used for when and do parts of a transitions

	*/



	/*

	// fqn could be trans or state
	private Expr dashRefVar(StateTable st, TransTable tt, String xType, Expr exp, List<String> region, String fqn, List<Integer> paramsIdx, List<String> params) {

		// Join: b1.a1.var

		// DashRefProcessRef: A/B/C[a1,b1]/var which became $$PROCESSREF$$. b1.a1.A/B/C/var in parsing
		// a DashRefProcessRef could be either a value for an exp
		// or a tuple for an event

		// BadJoin: var[a1,b1] which became b1.a1.var in parsing 

		// don't include isDashRefArrow here because that is only possible for 
		// events (which are tuples) not actions

		// turns PRIME(v) into v' 

		String v;
		List<Integer> paramsIdx 
		List<Expr> paramValues;
		if (isExprVar(exp)) {
			v = getVarName((ExprVar) exp);	
			if (v.startsWith(thisName)) {
				// thisSname gets replaced with p0_AID as a normal variable
				// not a processref
				String suffix = v.substring(thisName.length(),v.length());
				List<String> match = new ArrayList<String>();
				for (String x:region) 
					if (x.endsWith(suffix)) {
						// x must exist because in region
						Integer x = DashUtilFcns.lastElement(st.getParamsIdx(x));
						String p = DashUtilFcns.lastElement(st.getParams(x));
						match.add(Common.paramVar(x,p));
					}
				if (match.size() == 1)
					return match.get(0);
				else if (match.size() > 1)
					DashErrors.ambiguousUseOfThis(exp.toString());
				// else we carry on with it as a regular var name 
			}
			paramValues = new ArrayList<Expr>();
		} else if (isPrimedVar(exp)) {
			v = getVarName((ExprVar) getSub(exp))+PRIME;	
			paramValues = new ArrayList<Expr>();			
		} else {
			// name might not be fully resolved
			v = DashRef.nameOfDashRefExpr(exp);
			// have to recurse through param values
			paramValues = DashRef.paramValuesOfDashRefExpr(exp).stream()
						.map(i -> resolveExpr(st, xType, i, region, fqn, paramsIdx, params))
						.collect(Collectors.toList());
		}
		String vfqn = DashFQN.fqn(v);
		Boolean isPrimed = false;
		if (hasPrime(v)) {
			isPrimed = true;
			vfqn = removePrime(vfqn); // vfqn.substring(0,vfqn.length()-1);

		}
		
		// only place primes can be is in "do" expressions
		if (!xType.equals("do") && isPrimed) {
			DashErrors.noPrimedVarsIn(xType, v, fqn);
			return null;
		}
		List<String> matches = new ArrayList<String>();
		if (paramValues.isEmpty()) {
			// if no param values must be within the region of the same params (could be prefix of params)
			for (String s:region) 
				// buffers and vars
				for (String x:getNamesOfState(s)) {
					if (DashFQN.suffix(x,vfqn)) matches.add(x);
				}
		} else {
			// if it has params values, could be suffix of any var
			// and later we check it has the right number of params
			// vars and buffers
			for (String x:getAllNames()) {
				if (DashFQN.suffix(x,vfqn)) matches.add(x);
			}		
		}
		//System.out.println("vfqn: " + vfqn);
		//System.out.println("matches: "+ matches);
		//System.out.println("region: " + region);

		if (matches.size() > 1) {
			DashErrors.ambiguousVar(xType, v, fqn);
			return null; 
		} else if (matches.isEmpty()) {
			// its some var other than a dynamic variable
			return exp;
		} else {
			String m = matches.get(0);	
			if (paramValues.isEmpty()) {
				// must have same param values as trans b/c in same conc region
				if (getParams(m).size() > paramsIdx.size()) {
					// getRegion did not return things that all
					// have the same parameter values
					DashErrors.regionMatchesWrongParamNumber();
					return null;
				} else {
					// could be a subset of transition param values					
					List<Expr> prmValues = 
						Common.paramVars(
							paramsIdx.subList(0, getParams(m).size()),
							params.subList(0,getParams(m).size()));
					if (isPrimed)  m = m + PRIME;
					//System.out.println("here1" + m);
					return DashRef.DashRefExpr(m, prmValues);							
				}
			} else if (getParams(m).size() != paramValues.size()) { 
				// came with parameters so must be right number
				DashErrors.fqnVarWrongNumberParameters(xType, v, fqn); 
				return null;
			} else {
				if (isPrimed && !isInternal(m)) { 
					DashErrors.cantPrimeAnExternal(v, fqn);
					return null;
				}
				if (isPrimed) m = m+PRIME;
				//System.out.println("here2" + m);
				return DashRef.DashRefExpr(
					m, 
					// have to recursive through expressions in parameters
					paramValues.stream()
						.map(i -> resolveExpr(st, xType, i, region, fqn, paramsIdx,params))
						.collect(Collectors.toList()));
			}
		}
	}
	*/

	// must be done after resolve
	// might be primed or unprimed
	public List<DashRef> collectDashRefs(Expr exp) {
		List<DashRef> x = new ArrayList<DashRef>();
		if (DashRef.isDashRef(exp)) {
			x.add((DashRef) exp);
			return x;
		} else if (isExprBinary(exp)) {
			x.addAll(collectDashRefs(getLeft(exp)));
			x.addAll(collectDashRefs(getRight(exp)));
			return x;
		} else if (isExprBadJoin(exp)) {
			x.addAll(collectDashRefs(getLeft(exp)));
			x.addAll(collectDashRefs(getRight(exp)));
			return x;
		} else if (exp instanceof ExprCall) {
			for (Expr e: ((ExprCall) exp).args) x.addAll(collectDashRefs(e));
			return x;
		} else if (exp instanceof ExprChoice){
			for (Expr e: ((ExprChoice) exp).choices) x.addAll(collectDashRefs(e));
			return x;
		} else if (exp instanceof ExprITE){
			x.addAll(collectDashRefs(getCond(exp)));
			x.addAll(collectDashRefs(getLeft(exp)));
			x.addAll(collectDashRefs(getRight(exp)));
			return x;
		} else if (exp instanceof ExprList){
			for (Expr e: ((ExprCall) exp).args) x.addAll(collectDashRefs(e));
			return x;
		} else if (exp instanceof ExprUnary){
			return collectDashRefs(((ExprUnary) exp).sub);
		} else if (exp instanceof ExprLet){
			x.addAll(collectDashRefs(((ExprLet) exp).expr));
			x.addAll(collectDashRefs(((ExprLet) exp).sub));
			return x;
		} else if (exp instanceof ExprQt){
			List<Expr> ll = ((ExprQt) exp).decls.stream()
				.map(i -> i.expr)
				.collect(Collectors.toList());
			for (Expr e: ll) x.addAll(collectDashRefs(e));
			x.addAll(collectDashRefs(((ExprQt) exp).sub));
			return x;
		} else if (exp instanceof ExprConstant){
			return new ArrayList<DashRef>();
		} else {
			DashErrors.UnsupportedExpr("collectDashRefs", "");
			return null;
		}
	}

	// returns the primed variables in an exp (but w/o the primes)
	public List<DashRef> primedDashRefs(Expr exp) {
		List<DashRef> drs = collectDashRefs(exp);
		List<DashRef> o = new ArrayList<DashRef>();
		String v;
		List<Expr> paramValues;
		for (DashRef e: drs) {
			v = e.getName();
			paramValues = e.getParamValues();
			if (hasPrime(v)) {
				o.add(DashRef.createVarDashRef(removePrime(v), paramValues));
			}
		}
		return o;
	}
}