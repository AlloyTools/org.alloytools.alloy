package ca.uwaterloo.watform.parser;

import java.util.Set;
import java.util.List;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Collections;
import java.util.stream.Collectors;


import edu.mit.csail.sdg.ast.*;
import edu.mit.csail.sdg.alloy4.ConstList;

import static ca.uwaterloo.watform.alloyasthelper.ExprHelper.*;

import ca.uwaterloo.watform.core.*;
import static ca.uwaterloo.watform.core.DashUtilFcns.*;
import static ca.uwaterloo.watform.core.DashStrings.*;
import ca.uwaterloo.watform.core.DashRef;

public class VarTable {

	// stores Var, Buffer Decls in a HashMap based on the event FQN

	private HashMap<String,VarElement> varTable;
	private HashMap<String,BufferElement> bufferTable;

	public VarTable() {
		this.varTable = new HashMap<String,VarElement>();
		this.bufferTable = new HashMap<String,BufferElement>();
	}

	public class VarElement {
		private IntEnvKind kind;
		private List<String> params;
		private Expr typ;

		public VarElement(
			IntEnvKind k,
			List<String> prms,
			Expr t) {
			assert(prms != null);
			this.kind = k;
			this.params = prms;
			this.typ = t;
		}
		public String toString() {
			String s = new String();
			s += "kind: "+kind+"\n";
			s += "params: "+ NoneStringIfNeeded(params) +"\n";
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
	public Boolean addVar(String vfqn, IntEnvKind k, List<String> prms, Expr t) {
		assert(prms!=null);
		if (varTable.containsKey(vfqn)) return false;
		if (hasPrime(vfqn)) { DashErrors.nameShouldNotBePrimed(vfqn); return false; }
		else { varTable.put(vfqn, new VarElement(k,prms, t)); return true; }
	}
	public void resolve() {
		//anything?
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
	public List<String> getParams(String fqn) {
		if (bufferTable.containsKey(fqn)) return bufferTable.get(fqn).params;
		if (varTable.containsKey(fqn)) return varTable.get(fqn).params;
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
		private String element;
		private Integer index;

		public BufferElement(
			IntEnvKind k,
			List<String> prms,
			String e,
			Integer idx) {
			assert(prms != null);
			this.kind = k;
			this.params = prms;
			this.element = e;
			this.index = idx;
		}
		public String toString() {
			String s = new String();
			s += "kind: "+kind+"\n";
			s += "params: "+ NoneStringIfNeeded(params) +"\n";
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

	public Boolean addBuffer(String vfqn, IntEnvKind k, List<String> prms, String el, Integer idx) {
		assert(prms!=null);
		if (bufferTable.containsKey(vfqn)) return false;
		else { bufferTable.put(vfqn, new BufferElement(k,prms, el, idx)); return true; }
	}


	/*
		results in an Expr for the action that has all references to variables as DashRefExpr's
		fqn is a parameter to determine transition parameters and for error messages
		used for when and do parts of a transitions

	*/



	//TODO should probably be a visitor using accept methods of Expr
	// have to recurse through exp types, replace dynamic vars with DashRef and rebuild exp
	// don't use ExprHelper much here because we want to 
	// as much about the expression as possible
	public Expr resolveExpr(String xType, Expr exp, List<String> region,  String fqn, List<String> params) {
		//System.out.println(exp);
		if (isExprVar(exp)  ||
			isPrimedVar(exp) ||
			//DashRef.isDashRefJoin(exp) || 
			DashRef.isDashRefProcessRef(exp)) // || 
			//DashRef.isDashRefBadJoin(exp)) 
			{
				return dashRefVar(xType, exp, region,  fqn, params);

		} else if (isExprBinary(exp)) {
			return ((ExprBinary) exp).op.make(
				exp.pos,
				exp.closingBracket,
				resolveExpr(xType, getLeft(exp), region, fqn, params),
				resolveExpr(xType, getRight(exp), region, fqn, params));

		} else if (isExprBadJoin(exp)) {
			return ExprBadJoin.make(
				exp.pos,
				exp.closingBracket,
				resolveExpr(xType, getLeft(exp), region, fqn, params),
				resolveExpr(xType, getRight(exp), region, fqn, params));

		} else if (exp instanceof ExprCall) {
			return ExprCall.make(
				exp.pos, 
				exp.closingBracket,
				((ExprCall) exp).fun, 
				((ExprCall) exp).args.stream()
				.map(i -> resolveExpr(xType, i, region, fqn, params))
				.collect(Collectors.toList()), 
				((ExprCall) exp).extraWeight);

		} else if (exp instanceof ExprChoice){
			//TODO: check into this cast
			// not sure why is it necessary
			ConstList<Expr> x = (ConstList<Expr>) ((ExprChoice) exp).choices.stream()
					.map(i -> resolveExpr(xType, i, region, fqn, params))
					.collect(Collectors.toList());
			return ExprChoice.make(
				false,
				exp.pos, 
				x,
				((ExprChoice) exp).reasons);

		} else if (exp instanceof ExprITE){
			return ExprITE.make(
				exp.pos,
				resolveExpr(xType, getCond(exp), region, fqn, params),
				resolveExpr(xType, getLeft(exp), region, fqn, params),
				resolveExpr(xType, getRight(exp), region, fqn, params));

		} else if (exp instanceof ExprList){
            return ExprList.make(
            	exp.pos, 
            	exp.closingBracket,
            	((ExprList) exp).op,
            	((ExprList) exp).args.stream()
					.map(i -> resolveExpr(xType, i, region, fqn, params))
					.collect(Collectors.toList())
            );			

		} else if (exp instanceof ExprUnary){
			return ((ExprUnary) exp).op.make(
				exp.pos,
				resolveExpr(xType, ((ExprUnary) exp).sub, region, fqn, params));

		} else if (exp instanceof ExprLet){
			//TODO rule out var name
			return ExprLet.make(
				exp.pos, 
				((ExprLet) exp).var, 
				resolveExpr(xType, ((ExprLet) exp).expr, region, fqn, params),
				resolveExpr(xType, ((ExprLet) exp).sub, region, fqn, params));

		} else if (exp instanceof ExprQt){
			//TODO rule out var names in delcs as dynamic vars later

			// have to convert the expressions in the decls too
			List<Decl> decls = ((ExprQt) exp).decls.stream()
				.map(i -> new Decl(
					i.isPrivate,
					i.disjoint,
					i.disjoint2,
					i.isVar,
					i.names,
					resolveExpr(xType, i.expr, region, fqn, params)))
				.collect(Collectors.toList());

			return ((ExprQt) exp).op.make(
				exp.pos, 
				exp.closingBracket,  
				decls, 
				resolveExpr(xType, ((ExprQt) exp).sub, region, fqn, params));

		} else if (exp instanceof ExprConstant){
			return exp;

		} else {
			DashErrors.UnsupportedExpr(xType, fqn);
			return null;
		}
	}

	// fqn could be trans or state
	private Expr dashRefVar(String xType, Expr exp, List<String> region, String fqn, List<String> params) {

		// Join: b1.a1.var

		// DashRefProcessRef: A/B/C[a1,b1]/var which became $$PROCESSREF$$. b1.a1.A/B/C/var in parsing
		// a DashRefProcessRef could be either a value for an exp
		// or a tuple for an event

		// BadJoin: var[a1,b1] which became b1.a1.var in parsing 

		// don't include isDashRefArrow here because that is only possible for 
		// events (which are tuples) not actions

		// turns PRIME(v) into v' 

		String v;
		List<Expr> paramValues;
		if (isExprVar(exp)) {
			v = getVarName((ExprVar) exp);	
			if (v.startsWith(thisName)) {
				// thisAID gets replaced with pAID as a normal variable
				// not a processref
				String suffix = v.substring(thisName.length(),v.length());
				String match = "";
				for (String x:params) 
					if (x.equals(suffix))
						match = x;
				if (!match.isEmpty())
					return createVar(pName+match);
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
						.map(i -> resolveExpr(xType, i, region, fqn, params))
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
				if (getParams(m).size() > params.size()) {
					// getRegion did not return things that all
					// have the same parameter values
					DashErrors.regionMatchesWrongParamNumber();
					return null;
				} else {
					// could be a subset of transition param values					
					List<Expr> prmValues = 
						createVarList(
							DashStrings.pName,
							params.subList(0, getParams(m).size()));
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
						.map(i -> resolveExpr(xType, i, region, fqn, params))
						.collect(Collectors.toList()));
			}
		}
	}

	// must be done after resolve
	// might be primed or unprimed
	public List<Expr> collectDashRefs(Expr exp) {
		if (DashRef.isDashRefProcessRef(exp)) {
			List<Expr> x = new ArrayList<Expr>();
			x.add(exp);
			return x;
		} else if (isExprBinary(exp)) {
			List<Expr> x = new ArrayList<Expr>(collectDashRefs(getLeft(exp)));
			x.addAll(collectDashRefs(getRight(exp)));
			return x;
		} else if (isExprBadJoin(exp)) {
			List<Expr> x = new ArrayList<Expr>(collectDashRefs(getLeft(exp)));
			x.addAll(collectDashRefs(getRight(exp)));
			return x;
		} else if (exp instanceof ExprCall) {
			List<Expr> x = new ArrayList<Expr>();
			for (Expr e: ((ExprCall) exp).args) x.addAll(collectDashRefs(e));
			return x;
		} else if (exp instanceof ExprChoice){
			List<Expr> x = new ArrayList<Expr>();
			for (Expr e: ((ExprChoice) exp).choices) x.addAll(collectDashRefs(e));
			return x;
		} else if (exp instanceof ExprITE){
			List<Expr> x = new ArrayList<Expr>(collectDashRefs(getCond(exp)));
			x.addAll(collectDashRefs(getLeft(exp)));
			x.addAll(collectDashRefs(getRight(exp)));
			return x;
		} else if (exp instanceof ExprList){
			List<Expr> x = new ArrayList<Expr>();
			for (Expr e: ((ExprCall) exp).args) x.addAll(collectDashRefs(e));
			return x;
		} else if (exp instanceof ExprUnary){
			return collectDashRefs(((ExprUnary) exp).sub);
		} else if (exp instanceof ExprLet){
			List<Expr> x = new ArrayList<Expr>(collectDashRefs(((ExprLet) exp).expr));
			x.addAll(collectDashRefs(((ExprLet) exp).sub));
			return x;
		} else if (exp instanceof ExprQt){
			List<Expr> x = new ArrayList<Expr>();
			List<Expr> ll = ((ExprQt) exp).decls.stream()
				.map(i -> i.expr)
				.collect(Collectors.toList());
			for (Expr e: ll) x.addAll(collectDashRefs(e));
			x.addAll(collectDashRefs(((ExprQt) exp).sub));
			return x;
		} else if (exp instanceof ExprConstant){
			return new ArrayList<Expr>();
		} else {
			DashErrors.UnsupportedExpr("collectDashRefs", "");
			return null;
		}
	}

	// returns the primed variables in an exp (but w/o the primes)
	public List<Expr> primedDashRefs(Expr exp) {
		List<Expr> drs = collectDashRefs(exp);
		List<Expr> o = new ArrayList<Expr>();
		String v;
		List<Expr> paramValues;
		for (Expr e: drs) {
			v = DashRef.nameOfDashRefExpr(e);
			paramValues = DashRef.paramValuesOfDashRefExpr(e);
			if (hasPrime(v)) {
				o.add(DashRef.DashRefExpr(removePrime(v), paramValues));
			}
		}
		return o;
	}
}