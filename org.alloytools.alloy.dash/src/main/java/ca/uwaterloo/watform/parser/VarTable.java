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

	// stores Var Decls in a HashMap based on the event FQN

	private HashMap<String,VarElement> table;


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
	}

	public VarTable() {
		this.table = new HashMap<String,VarElement>();
	}
	public String toString() {
		String s = new String("VAR TABLE\n");
		for (String k:table.keySet()) {
			s += " ----- \n";
			s += k + "\n";
			s += table.get(k).toString();
		}
		return s;
	}	
	public Boolean add(String vfqn, IntEnvKind k, List<String> prms, Expr t) {
		assert(prms!=null);
		if (table.containsKey(vfqn)) return false;
		if (hasPrime(vfqn)) { DashErrors.nameShouldNotBePrimed(vfqn); return false; }
		else { table.put(vfqn, new VarElement(k,prms, t)); return true; }
	}
	public void resolveAllVarTable() {
		// TODO
	}
	public List<String> getAllVarNames() {
		return new ArrayList<String>(table.keySet());
	}
	public List<String> getParams(String vfqn) {
		if (table.containsKey(vfqn)) return table.get(vfqn).params;
		else { DashErrors.varDoesNotExist("getParams", vfqn); return null; }
	}
	public Expr getType(String vfqn) {
		if (table.containsKey(vfqn)) return table.get(vfqn).typ;
		else { DashErrors.varDoesNotExist("getType", vfqn); return null; }
	}

	public List<String> allVarsOfState(String sfqn) {
		// return all events declared in this state
		// will have the sfqn as a prefix
		return table.keySet().stream()
			// prefix of vfqn are state names
			.filter(i -> DashFQN.chopPrefixFromFQN(i).equals(sfqn))
			.collect(Collectors.toList());	
	}

	/*
		results in an Expr for the action that has all references to variables as DashRefExpr's
		fqn is a parameter to determine transition parameters and for error messages
		used for when and do parts of a transitions

		TODO: buffers, this
	*/
	public Expr resolveExprList(String xType, List<Expr> expList, List<String> region, String fqn, List<String> params) {
		if (expList.isEmpty()) return null;
		else if (expList.size() > 1) {
			DashErrors.tooMany(xType, fqn);
			return null;
		} else {
			Expr exp = expList.get(0);


			return resolveExpr(xType, exp, region, fqn, params);
		}
	}

	//TODO should probably be a visitor using accept methods of Expr
	// have to recurse through exp types, replace dynamic vars with DashRef and rebuild exp
	// don't use ExprHelper much here because we want to 
	// as much about the expression as possible
	public Expr resolveExpr(String xType, Expr exp, List<String> region, String fqn, List<String> params) {
		if (isExprVar(exp)  ||
			//DashRef.isDashRefJoin(exp) || 
			DashRef.isDashRefProcessRef(exp)) // || 
			//DashRef.isDashRefBadJoin(exp)) 
			{
				return dashRefVar(xType, exp, region, fqn, params);

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
			//TODO rule out var names
			return ((ExprQt) exp).op.make(
				exp.pos, 
				exp.closingBracket,  
				((ExprQt) exp).decls, 
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


		String v;
		List<Expr> paramValues;
		if (isExprVar(exp)) {
			v = getVarName((ExprVar) exp);	
			paramValues = new ArrayList<Expr>();
		} else {
			v = DashRef.nameOfDashRefExpr(exp);
			paramValues = DashRef.paramValuesOfDashRefExpr(exp);
		}
		String vfqn = DashFQN.fqn(v);
		Boolean isPrimed = false;
		if (hasPrime(v)) {
			isPrimed = true;
			vfqn = vfqn.substring(0,vfqn.length()-1);
		}
		

		if (!xType.equals("do") && isPrimed) {
			DashErrors.noPrimedVarsIn(xType, v, fqn);
			return null;
		}
		List<String> matches = new ArrayList<String>();
		for (String s:region) 
			for (String x:allVarsOfState(s)) {
				if (DashFQN.suffix(x,vfqn)) matches.add(x);
			}
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
					return DashRef.DashRefExpr(m, prmValues);							
				}
			} else if (getParams(m).size() != paramValues.size()) { 
				// came with parameters so must be right number
				DashErrors.fqnVarWrongNumberParameters(xType, v, fqn); 
				return null;
			} else {
				if (isPrimed) m = m+PRIME;
				return DashRef.DashRefExpr(
					m, 
					// have to recursive through expressions in parameters
					paramValues.stream()
						.map(i -> resolveExpr(xType, i, region, fqn, params))
						.collect(Collectors.toList()));
			}
		}
	}
}