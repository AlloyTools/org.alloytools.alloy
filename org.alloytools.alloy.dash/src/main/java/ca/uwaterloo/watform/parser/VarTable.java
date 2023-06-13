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
import ca.uwaterloo.watform.parser.PredTable;

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

	public void resolve(StateTable st, EventTable et, PredTable pt) {

		for (String vfqn: varTable.keySet()) {
			String sfqn = DashFQN.chopPrefixFromFQN(vfqn);
			setVarType(vfqn,ResolveExpr.resolveExpr(st, et, this, pt, "var", false, false, true, sfqn,getVarType(vfqn) ));
		}
		/* buffer types don't need resolving because just buf[element] */


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






	// must be done after resolve
	// might be primed or unprimed
	public List<DashRef> collectDashRefs(Expr exp) {
		assert(exp != null);
		List<DashRef> x = new ArrayList<DashRef>();
		if (DashRef.isDashRef(exp)) {
			x.add((DashRef) exp);
			return x;
		} else if (isExprVar(exp)) {
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
			for (Expr e: ((ExprList) exp).args) x.addAll(collectDashRefs(e));
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
			DashErrors.UnsupportedExpr("collectDashRefs", exp.toString());
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