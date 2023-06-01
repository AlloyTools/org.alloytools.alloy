package ca.uwaterloo.watform.parser;

import java.util.List;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Collections;
import java.util.stream.Collectors;

import edu.mit.csail.sdg.alloy4.Pos;

import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprLet;
import edu.mit.csail.sdg.ast.ExprBadJoin;
import edu.mit.csail.sdg.ast.ExprCall;
import edu.mit.csail.sdg.ast.ExprChoice;
import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.ast.ExprITE;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.Decl;

import static ca.uwaterloo.watform.core.DashUtilFcns.*;
import static ca.uwaterloo.watform.core.DashStrings.*;
import ca.uwaterloo.watform.core.DashErrors;
import ca.uwaterloo.watform.core.DashFQN;
import ca.uwaterloo.watform.core.DashRef;

import static ca.uwaterloo.watform.alloyasthelper.ExprHelper.*;
import ca.uwaterloo.watform.dashtoalloy.Common;


public class ResolveExpr{

	// returns an Expr (could be a DashRef) or raises an exception
	// can be used for expr, event uses, state uses
	// returned DashRef might have to be converted to a tuple for a state or an event in translation

	//TODO should probably be a visitor using accept methods of Expr
	// have to recurse through exp types, replace dynamic vars with DashRef and rebuild exp
	// don't use ExprHelper much here because we want to 
	// as much about the expression as possible
	public static Expr resolveExpr(	StateTable st, 
							EventTable et, 
							VarTable vt,
							String kind,
							boolean primeOk,
							boolean primeOkInPrmValues,
							boolean thisOk,
							String sfqn,  // could be parent of event or trans 
							Expr exp) {

		if (isExprVar(exp)  ||
			isPrimedVar(exp) ||
			DashRef.isDashRef(exp)) 
			{
				return resolveDashRef(st, et, vt, kind, primeOk, primeOkInPrmValues, thisOk, sfqn, exp);

		} else if (isExprBinary(exp)) {
			return ((ExprBinary) exp).op.make(
				exp.pos,
				exp.closingBracket,
				resolveExpr(st, et, vt, kind, primeOk, primeOkInPrmValues, thisOk, sfqn, getLeft(exp)),
				resolveExpr(st, et, vt, kind, primeOk, primeOkInPrmValues, thisOk, sfqn, getRight(exp)));

		} else if (isExprBadJoin(exp)) {
			return ExprBadJoin.make(
				exp.pos,
				exp.closingBracket,
				resolveExpr(st, et, vt, kind, primeOk, primeOkInPrmValues, thisOk, sfqn, getLeft(exp)),
				resolveExpr(st, et, vt, kind, primeOk, primeOkInPrmValues, thisOk, sfqn, getRight(exp)));

		} else if (exp instanceof ExprCall) {
			return ExprCall.make(
				exp.pos, 
				exp.closingBracket,
				((ExprCall) exp).fun, 
				((ExprCall) exp).args.stream()
				.map(i -> resolveExpr(st, et, vt, kind, primeOk, primeOkInPrmValues, thisOk, sfqn, i))
				.collect(Collectors.toList()), 
				((ExprCall) exp).extraWeight);

		} else if (exp instanceof ExprChoice){
			//TODO: check into this cast
			// not sure why is it necessary
			ConstList<Expr> x = (ConstList<Expr>) ((ExprChoice) exp).choices.stream()
					.map(i -> resolveExpr(st, et, vt, kind, primeOk, primeOkInPrmValues, thisOk, sfqn, i))
					.collect(Collectors.toList());
			return ExprChoice.make(
				false,
				exp.pos, 
				x,
				((ExprChoice) exp).reasons);

		} else if (exp instanceof ExprITE){
			return ExprITE.make(
				exp.pos,
				resolveExpr(st, et, vt, kind, primeOk, primeOkInPrmValues, thisOk, sfqn, getCond(exp)),
				resolveExpr(st, et, vt, kind, primeOk, primeOkInPrmValues, thisOk, sfqn, getLeft(exp)),
				resolveExpr(st, et, vt, kind, primeOk, primeOkInPrmValues, thisOk, sfqn, getRight(exp)));

		} else if (exp instanceof ExprList){
            return ExprList.make(
            	exp.pos, 
            	exp.closingBracket,
            	((ExprList) exp).op,
            	((ExprList) exp).args.stream()
					.map(i -> resolveExpr(st, et, vt, kind, primeOk, primeOkInPrmValues, thisOk, sfqn, i))
					.collect(Collectors.toList())
            );			

		} else if (exp instanceof ExprUnary){
			return ((ExprUnary) exp).op.make(
				exp.pos,
				resolveExpr(st, et, vt, kind, primeOk, primeOkInPrmValues, thisOk, sfqn, ((ExprUnary) exp).sub));

		} else if (exp instanceof ExprLet){
			//TODO rule out var name
			return ExprLet.make(
				exp.pos, 
				((ExprLet) exp).var, 
				resolveExpr(st, et, vt, kind, primeOk, primeOkInPrmValues, thisOk, sfqn, ((ExprLet) exp).expr),
				resolveExpr(st, et, vt, kind, primeOk, primeOkInPrmValues, thisOk, sfqn, ((ExprLet) exp).sub) );

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
					resolveExpr(st, et, vt, kind, primeOk, primeOkInPrmValues, thisOk, sfqn, i.expr)))
				.collect(Collectors.toList());

			return ((ExprQt) exp).op.make(
				exp.pos, 
				exp.closingBracket,  
				decls, 
				resolveExpr(st, et, vt, kind, primeOk, primeOkInPrmValues, thisOk, sfqn,((ExprQt) exp).sub));

		} else if (exp instanceof ExprConstant){
			return exp;

		} else {
			DashErrors.UnsupportedExpr(exp.toString(), sfqn);
			return null;
		}
	}

	static Expr resolveDashRef(	StateTable st, 
							EventTable et, 
							VarTable vt,
							String kind,
							boolean primeOk,
							boolean primeOkInPrmValues,
							boolean thisOk,
							String sfqn,  // could be parent of event or trans 
							Expr exp) {

		// Join: b1.a1.var

		// DashRefProcessRef: A/B/C[a1,b1]/var which became $$PROCESSREF$$. b1.a1.A/B/C/var in parsing
		// a DashRefProcessRef could be either a value for an exp
		// or a tuple for an event

		// BadJoin: var[a1,b1] which became b1.a1.var in parsing 

		// don't include isDashRefArrow here because that is only possible for 
		// events (which are tuples) not actions

		// turns PRIME(v) into v' 

		assert(isExprVar(exp) || isPrimedVar(exp) || DashRef.isDashRef(exp));
		assert(kind.equals("state") || kind.equals("event") || kind.equals("var"));
		String v;
		List<Integer> paramsIdx = st.getParamsIdx(sfqn); 
		List<String> params = st.getParams(sfqn);

		List<Expr> paramValues = new ArrayList<Expr>();

		Boolean isPrimed = false;
		Pos pos = exp.pos();
		if (isExprVar(exp)) {
			// no param values
			v = getVarName((ExprVar) exp);

			if (thisOk && v.startsWith(thisName)) {
				// thisSname gets replaced with p0_AID as a normal variable
				// not a dashsref
				String suffix = v.substring(thisName.length(),v.length());
				List<String> matches = findMatchesInRegion(st,et,vt,"state",sfqn,suffix);
				if (matches.size() == 1 && st.hasParam(matches.get(0)))
					return Common.paramVar(st.getParamIdx(matches.get(0)), st.getParam(matches.get(0)));
				else if (matches.size() == 1 && !st.hasParam(matches.get(0)))
					DashErrors.nonParamUseOfThis(pos,exp.toString());
				else if (matches.size() > 1) {
					DashErrors.ambiguousUseOfThis(pos,exp.toString());
				}
				/* else we carry on with it as a regular var name with no params */
			}
		} else if (isPrimedVar(exp)) {
			// AlloyExpr is PrimeOp(name)
			//System.out.println("isPrimedVar");
			isPrimed = true;
			v = getVarName((ExprVar) getSub(exp));	
			if (!primeOk) { DashErrors.noPrimedVars(pos, exp.toString()); return null; }
		} else {
			// name might not be fully resolved
			// might have a prime on name 
			// due to the way DashRefs are parsed,
			// they are not turned into PrimeOp(name)
			v = ((DashRef) exp).getName();
			if (hasPrime(v)) {
				isPrimed = true;
				v = removePrime(v);
				if (!primeOk) { DashErrors.noPrimedVars(pos, exp.toString()); return null; }				
			}
			// have to recurse through param values as VARs
			paramValues = ((DashRef) exp).getParamValues().stream()
						.map(i -> resolveExpr(st, et, vt, "var", primeOkInPrmValues, primeOkInPrmValues, thisOk, sfqn, i))
						.collect(Collectors.toList());
		}
		// now we have v as the name, paramValues as the possible empty set of resolved param values
		// and isPrimed is set correctly
		//System.out.println("looking for "+v);
		List<String> matches;
		if (paramValues.isEmpty()) {
			// if no param values must be within region 
			// that has same param values
			matches = findMatchesInRegion(st,et,vt,kind,sfqn,v);
		} else {
			// if it has params values, could be suffix of any var
			// and later we check it has the right number of params
			matches = findMatches(st, et, vt, kind, v);	
		}
		//System.out.println(matches);
		if (matches.size() > 1) {
			DashErrors.ambiguousRef(pos, exp.toString());
			return null; 
		} else if (matches.isEmpty()) {
			if (kind.equals("state")) {DashErrors.unknownState(pos, exp.toString()); return null; }
			else if (kind.equals("event")) { DashErrors.unknownEvent(pos, exp.toString()); return null; }
			else { // it's some var other than a dynamic variable
				//System.out.println("no match: "+exp.toString());
				return exp;
			}
		} else {
			// one match
			String m = matches.get(0);
			List<String> mParams;
			if (kind.equals("state")) mParams = st.getParams(m);
			else if (kind.equals("event")) mParams = et.getParams(m);
			else mParams = vt.getParams(m);

			if (paramValues.isEmpty()) {
				// must have same param values as sfqn b/c in same region
				if (mParams.size() > paramsIdx.size()) {
					// getRegion did not return things that all
					// have the same parameter values

					DashErrors.wrongNumberParams(pos, exp.toString());
					return null;
				} else {
					// could be a subset of param values					
					paramValues = 
						Common.paramVars(
							paramsIdx.subList(0, mParams.size()),
							params.subList(0,mParams.size()));
				}
			} else if (mParams.size() != paramValues.size()) { 
				// came with parameters so must be right number
				//TODO could paramValues b less than mParams????
				// and paramValues be a suffix of mParams???
				// since the name can be a suffix
				DashErrors.wrongNumberParams(pos, exp.toString()); 
				return null;
			} else 

			if (isPrimed && kind.equals("var"))
				if (!vt.isInternal(m)) { 
					DashErrors.cantPrimeAnExternalVar(pos, v);
					return null;
				}
			if (isPrimed) m = m+PRIME;
			if (kind.equals("state")) { return DashRef.createStateDashRef(pos, m, paramValues); }
			else if (kind.equals("event")) { return DashRef.createEventDashRef(pos, m, paramValues); }
			else {
				//System.out.println(DashRef.createVarDashRef(pos, m, paramValues));
				return DashRef.createVarDashRef(pos, m, paramValues);
			}
		}
	}

	private static List<String> findMatchesInRegion(StateTable st, EventTable et, VarTable vt, String kind, String sfqn, String suffix) {
		
		List<String> region = new ArrayList<String>();
		if (kind.equals("state")) region = st.getRegion(sfqn);
		else if (kind.equals("event")) {
			for (String x: st.getRegion(sfqn)) region.addAll(et.getEventsOfState(x));
		} else if (kind.equals("var")) {
			for (String x: st.getRegion(sfqn)) { 
				region.addAll(vt.getVarsOfState(x)); 
				region.addAll(vt.getBuffersOfState(x));
			}
		}
		return compareMatches(suffix,region);
	}
	private static List<String> compareMatches(String suffix, List<String> region) {
		List<String> matches = new ArrayList<String>();
		for (String x:region) 
			// can't just end with the suffix b/c that might not be a complete name!
			// e.g., Chairs can match xChairs and yChairs but those are actually different identifiers!
			if (x.endsWith(suffix)) {
				// matches to the very beginning
				if (x.lastIndexOf(suffix) == 0) matches.add(x);
				// matches starts with a "/"
				else if (x.substring(x.lastIndexOf(suffix)-1,x.lastIndexOf(suffix)).equals("/")) matches.add(x);
			}
		return matches;
	}

	private static List<String> findMatches(StateTable st, EventTable et, VarTable vt, String kind, String suffix) {
		List<String> region = new ArrayList<String>();	
		if (kind.equals("state")) region.addAll(st.getAllStateNames());
		else if (kind.equals("event")) region.addAll(et.getAllEventNames());
		else if (kind.equals("var")) {
			region.addAll(vt.getAllVarNames());
			region.addAll(vt.getAllBufferNames());
		}
		return compareMatches(suffix,region);
	}
}