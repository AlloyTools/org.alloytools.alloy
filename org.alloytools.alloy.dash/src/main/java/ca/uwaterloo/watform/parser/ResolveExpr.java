/*
	This function takes an Expr and sorts out any Dash names used in it to:
	1) make the names fully qualified
	2) figure out all the parameter values
	3) figures out what "thisState" means
	4) turns PRIME(v) into v' 

	It is called from stateTable resolving for inits and invariants and that 
	It is called from varTable for resolving type of dynamic variables (where it resolves
	   only the name, not the parameters)
	It is called from transTable to resolve all parts of transitions.

	Variation points for these uses is in where to search for 
	a name (stateTable, EventTable, varTable)
	
	Incoming Expr may also be a DashRef (from parsing for src/dest/on/send).
	
	Errors are given using "pos".
*/
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
							PredTable pt,
							String kind,
							boolean primeOk,
							boolean primeOkInPrmValues,
							boolean thisOk,
							String sfqn,  // could be parent of event or trans 
							Expr exp) {
		//System.out.println("resolve: " + exp);
		if (isExprVar(exp)  ||
			isPrimedVar(exp) ||
			DashRef.isDashRef(exp)) 
			{
				return resolveDashRef(st, et, vt, pt,kind, primeOk, primeOkInPrmValues, thisOk, sfqn, exp);

		} else if (isExprBinary(exp)) {
			return ((ExprBinary) exp).op.make(
				exp.pos,
				exp.closingBracket,
				resolveExpr(st, et, vt, pt,kind, primeOk, primeOkInPrmValues, thisOk, sfqn, getLeft(exp)),
				resolveExpr(st, et, vt, pt,kind, primeOk, primeOkInPrmValues, thisOk, sfqn, getRight(exp)));

		} else if (isExprBadJoin(exp)) {
			return ExprBadJoin.make(
				exp.pos,
				exp.closingBracket,
				resolveExpr(st, et, vt, pt,kind, primeOk, primeOkInPrmValues, thisOk, sfqn, getLeft(exp)),
				resolveExpr(st, et, vt, pt,kind, primeOk, primeOkInPrmValues, thisOk, sfqn, getRight(exp)));

		} else if (exp instanceof ExprCall) {
			return ExprCall.make(
				exp.pos, 
				exp.closingBracket,
				((ExprCall) exp).fun, 
				((ExprCall) exp).args.stream()
				.map(i -> resolveExpr(st, et, vt, pt,kind, primeOk, primeOkInPrmValues, thisOk, sfqn, i))
				.collect(Collectors.toList()), 
				((ExprCall) exp).extraWeight);

		} else if (exp instanceof ExprChoice){
			//TODO: check into this cast
			// not sure why is it necessary
			ConstList<Expr> x = (ConstList<Expr>) ((ExprChoice) exp).choices.stream()
					.map(i -> resolveExpr(st, et, vt, pt,kind, primeOk, primeOkInPrmValues, thisOk, sfqn, i))
					.collect(Collectors.toList());
			return ExprChoice.make(
				false,
				exp.pos, 
				x,
				((ExprChoice) exp).reasons);

		} else if (exp instanceof ExprITE){
			return ExprITE.make(
				exp.pos,
				resolveExpr(st, et, vt, pt,kind, primeOk, primeOkInPrmValues, thisOk, sfqn, getCond(exp)),
				resolveExpr(st, et, vt, pt,kind, primeOk, primeOkInPrmValues, thisOk, sfqn, getLeft(exp)),
				resolveExpr(st, et, vt, pt,kind, primeOk, primeOkInPrmValues, thisOk, sfqn, getRight(exp)));

		} else if (exp instanceof ExprList){
            return ExprList.make(
            	exp.pos, 
            	exp.closingBracket,
            	((ExprList) exp).op,
            	((ExprList) exp).args.stream()
					.map(i -> resolveExpr(st, et, vt, pt,kind, primeOk, primeOkInPrmValues, thisOk, sfqn, i))
					.collect(Collectors.toList())
            );			

		} else if (exp instanceof ExprUnary){
			return ((ExprUnary) exp).op.make(
				exp.pos,
				resolveExpr(st, et, vt, pt,kind, primeOk, primeOkInPrmValues, thisOk, sfqn, ((ExprUnary) exp).sub));

		} else if (exp instanceof ExprLet){
			//TODO rule out var name
			return ExprLet.make(
				exp.pos, 
				((ExprLet) exp).var, 
				resolveExpr(st, et, vt, pt,kind, primeOk, primeOkInPrmValues, thisOk, sfqn, ((ExprLet) exp).expr),
				resolveExpr(st, et, vt, pt,kind, primeOk, primeOkInPrmValues, thisOk, sfqn, ((ExprLet) exp).sub) );

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
					resolveExpr(st, et, vt, pt,kind, primeOk, primeOkInPrmValues, thisOk, sfqn, i.expr)))
				.collect(Collectors.toList());

			return ((ExprQt) exp).op.make(
				exp.pos, 
				exp.closingBracket,  
				decls, 
				resolveExpr(st, et, vt, pt,kind, primeOk, primeOkInPrmValues, thisOk, sfqn,((ExprQt) exp).sub));

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
							PredTable pt,
							String kind,
							boolean primeOk,
							boolean primeOkInPrmValues,
							boolean thisOk,
							String sfqn,  // could be parent of event or trans 
							Expr exp) {


		assert(isExprVar(exp) || isPrimedVar(exp) || DashRef.isDashRef(exp));
		assert(kind.equals("state") || kind.equals("event") || kind.equals("var"));

		//System.out.println("in: " + exp);

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
				List<String> matches = findMatchesInRegion(st,et,vt,pt,"state",sfqn,suffix);
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
						.map(i -> resolveExpr(st, et, vt, pt,"var", primeOkInPrmValues, primeOkInPrmValues, thisOk, sfqn, i))
						.collect(Collectors.toList());
		}

		// now we have v as the name, paramValues as the possible empty set of resolved param values
		// and isPrimed is set correctly
		

		List<String> matches;
		if (paramValues.isEmpty()) {
			// if no param values must be within region 
			// that has same param values
			matches = findMatchesInRegion(st,et,vt,pt,kind,sfqn,v);
		} else {
			// if it has params values, could be suffix of any var
			// and later we check it has the right number of params
			matches = findMatches(st, et, vt, pt,kind, v);	
		}

		String m = "";
		if (matches.isEmpty()) {
			if (kind.equals("state")) {DashErrors.unknownState(pos, exp.toString()); return null; }
			else if (kind.equals("event")) { DashErrors.unknownEvent(pos, exp.toString()); return null; }
			else { 
					// it's some var other than a dynamic variable or a predicate name
					return exp;
			}
		} else {
			m = chooseMatch(sfqn, matches);
			if (m == null) {
				DashErrors.ambiguousRef(pos, exp.toString());
				return null; 
			}
			if (pt.contains(m))
				// best match is a predicate name
				// has to be treated a little differently
				// because does not have params and have to put its exp
				// directly in place unlike a DashRef
				// resolve the predicate value in place and add it in place
				return resolveExpr(st,et,vt,pt,"var",primeOkInPrmValues, primeOkInPrmValues, thisOk, sfqn, pt.getExp(m));
		}

		// m is one match from var/state or event table
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
			Expr out = DashRef.createVarDashRef(pos, m, paramValues);
			//System.out.println("out: " + out);
			return out;
		}
	}

	private static List<String> findMatchesInRegion(StateTable st, EventTable et, VarTable vt, PredTable pt, String kind, String sfqn, String suffix) {
		
		List<String> region = new ArrayList<String>();
		if (kind.equals("state")) region = st.getRegion(sfqn);
		else if (kind.equals("event")) {
			for (String x: st.getRegion(sfqn)) region.addAll(et.getEventsOfState(x));
		} else if (kind.equals("var")) {
			for (String x: st.getRegion(sfqn)) { 
				region.addAll(vt.getVarsOfState(x)); 
				region.addAll(vt.getBuffersOfState(x));
				// does not have to have to be within state
				// because does not take parameter values
			}
			region.addAll(pt.getAllNames());
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

	private static List<String> findMatches(StateTable st, EventTable et, VarTable vt, PredTable pt, String kind, String suffix) {
		List<String> region = new ArrayList<String>();	
		if (kind.equals("state")) region.addAll(st.getAllStateNames());
		else if (kind.equals("event")) region.addAll(et.getAllEventNames());
		else if (kind.equals("var")) {
			region.addAll(vt.getAllVarNames());
			region.addAll(vt.getAllBufferNames());
			region.addAll(pt.getAllNames());
		}
		return compareMatches(suffix,region);
	}


	private static String chooseMatch(String sfqn, List<String> matches) {
		// get highest rank match based on sfqn
		// if two have same rank, then ambiguous
		int longestCommonPrefix = 0;
		String bestmatch = "";
		Boolean multipleBestMatches = false;
		for (String s: matches) {
			if (DashFQN.commonPrefixLength(sfqn,s) > longestCommonPrefix) {
				longestCommonPrefix = DashFQN.commonPrefixLength(sfqn,s);
				bestmatch = s;
				multipleBestMatches = false;
			} else if (DashFQN.commonPrefixLength(sfqn,s) == longestCommonPrefix) {
				multipleBestMatches = true;
			}
		}
		if (!multipleBestMatches && longestCommonPrefix > 0) {
			return bestmatch;
		} else {	
			return null; 					
		}
	}

}

		/*
		// there is one or more match
		// sfqn is the context 
		// might be a suffix of the name, not just v
		String m = "";
		if (matches.size() >= 1) {
			if (matches.contains(DashFQN.mergeFQN(sfqn,v)) || matches.contains(sfqn)) {
				// first choice: if a match is sfqn+/+v or sfqn itself 
				// that's the best match (if both are in matches then ambiguous)
				if (matches.contains(DashFQN.fqn(sfqn,v))) {
					if (matches.contains(sfqn)) {
						DashErrors.ambiguousRef(pos, exp.toString());
						return null; 						
					} else {
						m = sfqn;
					}
				} else {
					m = DashFQN.mergeFQN(sfqn,v);
				}
			} else {
				List<String> matchesWithinSfqn = matches.stream()
					.filter(i -> i.startsWith(sfqn))
					.collect(Collectors.toList());
				if (matchesWithinSfqn.size() > 0) {
					// next best is something internal to sfqn so match is sfqn / .... / v (must only one)
					if (matchesWithinSfqn.size() == 1) m = matchesWithinSfqn.get(0);
					else {
						DashErrors.ambiguousRef(pos, exp.toString());
						return null; 						
					}
				} else {
					// Final choice is something external to sfqn (must be only one)
					if (matches.size() > 1) {
						DashErrors.ambiguousRef(pos, exp.toString());
						return null;
					} else {
						m = matches.get(0);
					} 				
				}
			}
		} 
		*/