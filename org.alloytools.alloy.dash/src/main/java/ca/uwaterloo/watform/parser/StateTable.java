/*  The StateTable maps:
	FullyQualStateName -> info about state

	It is created during the resolveAll phase.
*/

package ca.uwaterloo.watform.parser;

import java.io.*;

import java.util.Set;
import java.util.HashMap;
import java.util.List;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Collections;
import java.util.stream.Collectors;

import edu.mit.csail.sdg.ast.Expr;

import ca.uwaterloo.watform.core.*;
import ca.uwaterloo.watform.core.DashRef;
import static ca.uwaterloo.watform.core.DashUtilFcns.*;
import static ca.uwaterloo.watform.core.DashStrings.*;
import static ca.uwaterloo.watform.core.DashFQN.*;
import ca.uwaterloo.watform.alloyasthelper.ExprHelper;

import ca.uwaterloo.watform.ast.*;

import ca.uwaterloo.watform.parser.VarTable;
import ca.uwaterloo.watform.dashtoalloy.Common;

public class StateTable {
	private HashMap<String,StateElement> table;
	private boolean isResolved;
	private String root;
	private List<Expr> inits = new ArrayList<Expr>();
	private List<Expr> invs  = new ArrayList<Expr>();
	private List<String> allParamsInOrder = new ArrayList<String>();

	public Integer addToParamsList(String p) {
		allParamsInOrder.add(p);
		return allParamsInOrder.size()-1;
	}
	private String space = " ";

	/* nested class for elementes in the state table */
	public class StateElement {
		// better than a tuple
		private DashStrings.StateKind kind; // must exist AND/OR
		private String param; // may be empty
		private List<String> params; // null if none; param is last of params if it exists
		private List<Integer> paramsIdx; // their pos in the list of params (will be a sequence)
		private DashStrings.DefKind def; 
		// these all use fullQual names to point to trans in TransTable
		// or states in this StateTable
		private String parent; // null if none
		// this could be a set b/c there are no dups and order
		// doesn't matter, but lists are easier to work with
		private List<String> immChildren; // empty if none
		private List<DashInv> origInvariants;
		private List<DashInit> origInits;
		// this aren't resolved here
		// so no need to keep original separate from resolved
		private List<Expr> entered;
		private List<Expr> exited;
		//private List<DashAction> actions;
		//private List<DashCondition> conditions;
		// after resolve
		private List<Expr> invs;
		private List<Expr> inits;


		public StateElement(
			DashStrings.StateKind k,
			String prm,
			List<String> prms, 
			List<Integer> prmsIdx,
			DashStrings.DefKind d,
			String p, 
			List<String> iChildren,
			List<DashInv> invL,
			List<DashInit> initL,
			List<Expr> entered,
			List<Expr> exited
			//List<DashAction> actL,
			//List<DashCondition> condL
		) {
		
			assert(k != null);
			assert(prm == null || !prm.isEmpty());
			assert(prms != null);
			assert(p == null || !p.isEmpty());
			assert(iChildren != null); // could be empty
			assert(invL != null);
			assert(initL != null);
			//assert(actL != null);
			//assert(condL != null);
			this.kind = k; 
			this.param = prm;
			this.params = prms; 
			this.paramsIdx = prmsIdx;
			this.def = d; 
			this.parent = p; 
			this.immChildren = iChildren; 
			this.origInvariants = invL;
			this.origInits = initL;
			this.entered = entered;
			this.exited = exited;
			//this.actions = actL;
			//this.conditions = condL;

		}
		public String toString() {
			String s = new String();
			s += "kind: "+kind +"\n";
			s += "param:"+ NoneStringIfNeeded(param)+"\n";
			s += "params: "+ NoneStringIfNeeded(params) +"\n";
			s += "default: "+def+"\n";
			s += "parent: "+ NoneStringIfNeeded(parent) +"\n";
			s += "immChildren: "+NoneStringIfNeeded(immChildren) +"\n";
			// add more
			return s;
		}


	}


	public StateTable() {
		this.table = new HashMap<String,StateElement>();
		this.isResolved = false;
	}
	public void setRoot(String s) {
		root = s;
	}
	public String getRoot() {
		return root;
	}
	public boolean isRoot(String s) {
		return (s.equals(getRoot()));
	}
	public String toString() {
		String s = new String("STATE TABLE\n");
		for (String k:table.keySet()) {
			s += " ----- \n";
			//System.out.println(s);
			s += k + "\n";
			//System.out.println(s);
			s += table.get(k).toString();
			//System.out.println(s);
		}
		return s;
	}
	public void add(String fqn) {
		assert(!fqn.isEmpty());
		if (!table.containsKey(fqn))
			table.put(fqn,null);
		//System.out.println("adding State table: "+fqn);
	}
	public boolean add(
		String fqn, 
		DashStrings.StateKind k, 
		String prm, 
		List<String> prms, 
		List<Integer> prmsIdx,
		DashStrings.DefKind d,
		String p, 
		List<String> iChildren,
		List<DashInv> invL,
		List<DashInit> initL,
		List<Expr> enteredL,
		List<Expr> exitedL)  {
		// if its null, make it empty to not throw exceptions
		//if (iChildren == null) iChildren = new ArrayList<String>();
		//if (table.containsKey(fqn)) {
		//	StateElement se = table.get(fqn);
		//	if (se == null) 
		//		table.replace(fqn, new StateElement(k,prm, prms,d, p,iChildren, invL, initL, actL, condL));
		//	else if (!se.attributesSame(k,prm,prms,d,p,iChildren)) 
				// hopefully not possible
				//DashErrors.addStateToStateTableDup(fqn);
		//}
		//else 
		if (table.containsKey(fqn)) return false;
		else if (DashStrings.hasPrime(fqn)) { DashErrors.nameShouldNotBePrimed(fqn); return false; }
		else { table.put(fqn, new StateElement(k,prm, prms,prmsIdx, d,p,iChildren, invL, initL, enteredL, exitedL)); return true; }
		//System.out.println("adding to State table: "+fqn+space+prm + space + prms+space+d+space+p+iChildren);
	}
	public void addInit(Expr exp) {
		inits.add(exp);
	}
	public void addInv(Expr exp) {
		invs.add(exp);
	}
	public boolean containsKey(String s) {
		return table.containsKey(s);
	}
	public boolean setAsDefault(String s) {
		if (table.containsKey(s)) {
			table.get(s).def = DashStrings.DefKind.DEFAULT;
			return true;
		}
		else { DashErrors.stateDoesNotExist("setDefault", s); return false; }		
	}
	public boolean isLeaf(String s)  {
		if (table.containsKey(s)) 
			return (table.get(s).immChildren.isEmpty());
		else { DashErrors.stateDoesNotExist("isLeaf", s); return false; }
	}
	public boolean isOr(String s) {
		if (table.containsKey(s)) 
			return (table.get(s).kind == StateKind.OR);
		else { DashErrors.stateDoesNotExist("isOr", s); return false; }
	}
	public boolean isAnd(String s) {
		if (table.containsKey(s)) 
			return (table.get(s).kind == StateKind.AND);
		else { DashErrors.stateDoesNotExist("isAnd",s); return false; }
	}
	public boolean isDefault(String s) {
		if (table.containsKey(s)) 
			return (table.get(s).def == DefKind.DEFAULT);
		else { DashErrors.stateDoesNotExist("isDefault",s); return false; }
	}
	public List<String> getAllStateNames() {
		return new ArrayList<String>(table.keySet());
	}
	public String getParam(String s) {
		if (table.containsKey(s))
			return table.get(s).param;  
		else { DashErrors.stateDoesNotExist("getParam", s); return null; }	
	}
	public Integer getParamIdx(String s) {
		if (table.containsKey(s) && hasParam(s))
			return lastElement(table.get(s).paramsIdx);  
		else { DashErrors.stateDoesNotExist("getParam", s); return null; }	
	}
	public boolean hasParam(String s) {
		if (table.containsKey(s))
			return table.get(s).param != null;  
		else { DashErrors.stateDoesNotExist("hasParam", s); return false; }			
	}
	public List<String> getParams(String s) {
		if (table.containsKey(s))
			return table.get(s).params;  
		else { DashErrors.stateDoesNotExist("getParams", s); return null; }
	}
	public List<Integer> getParamsIdx(String s) {
		if (table.containsKey(s))
			return table.get(s).paramsIdx;  
		else { DashErrors.stateDoesNotExist("getParamsIdx", s); return null; }		
	}
	public Boolean hasConcurrency(String s) {
		if (table.containsKey(s)) {
			if (table.get(s).kind == DashStrings.StateKind.AND) return true;
			else 
				for (String k: table.get(s).immChildren) {
					if (hasConcurrency(k)) return true;
				}
				return false;
		} else { DashErrors.stateDoesNotExist("hasConcurrency", s); return null; }
	}
	public String getParent(String child) {
		if (table.containsKey(child))
			return table.get(child).parent;  // could be null if root
		else { DashErrors.stateDoesNotExist("getParent", child); return null; }
	}
	public List<String> getImmChildren(String parent)  {
		if (table.containsKey(parent))
			return table.get(parent).immChildren;
		else { DashErrors.stateDoesNotExist("getImmChildren", parent); return null; }
	}
	public List<String> getAllAnces(String fqn) {
		// do not need to walk over tree for this operation; can just use FQNs
		List<String> fqnSplit = DashFQN.splitFQN(fqn);
		List<String> x = new ArrayList<String>();
		// include the state itself (could be Root)
		if (fqnSplit.size() > 0) for (int i=0; i < fqnSplit.size(); i++) x.add(DashFQN.fqn(fqnSplit.subList(0,i+1)));
		// list is in order from root, ...., fqn-1 on path
		//System.out.println("getAllAnces of "+fqn+" is "+x);
		// contains at least Root state
		return x;
	}

	public List<String> getAllPrefixParamAnces(String sfqn) {
		return getAllAnces(sfqn).stream()
			.filter(i -> (isAnd(i) && hasParam(i)) || isRoot(i))
			.collect(Collectors.toList());
	}
	// might not be used anymore
	public String getClosestParamAnces(String s) {				
		// getAllAnces returns list from Root, ..., parentFQN on path
		// could also just walk back through parents
		List<String> allAnces = getAllAnces(s);
		//allAnces.add(s);
		Collections.reverse(allAnces);

		String concAnces = null;
		// allAnces cannot be empty b/c must have Root in it
		for (String a:allAnces) {
			if (hasParam(a) || isRoot(a)) {
				concAnces = a;
				break;
			}
		}
		//System.out.println("getClosestConcAnces: "+concAnces);
		return concAnces; // might be null
	}
	

	public List<String> getAllNonParamDesc(String s) {
		// get all the descendants not WITHIN parameterized states
		// s is included
		// have to be careful to avoid duplicates
		List<String> desc = new ArrayList<String>();
		desc.add(s); // could be Root or a conc state

		if (table.containsKey(s)) {
			for (String c: table.get(s).immChildren) {
				//System.out.println("in getAllNonParamDesc: "+c);
				if (isOr(c) || !hasParam(c)) desc.addAll(getAllNonParamDesc(c));
			}
			return desc;
		} else { DashErrors.stateDoesNotExist("getAllNonParamDesc", s); return null; }	
	}
	// region is the area within which the src name does not need to be FQN
	public List<String> getRegion(String sfqn) {
		List<String> r = new ArrayList<String>();
		for (String s: getAllPrefixParamAnces(sfqn)) {
			r.addAll(getAllNonParamDesc(s));
		}
		return r;
	}
	public int getMaxDepthParams() {
		return getMaxDepthParams(root);
	}
	public int getMaxDepthParams(String s) {
		// TODO: check this - seems to be not getting to full depth
		int max = 0;
		for (String c: getImmChildren(s)) {
			if (getParams(c) != null) 
				if (max < getParams(c).size()) max = getParams(c).size();
			if (max < getMaxDepthParams(c)) max = getMaxDepthParams(c);
		}
		return max;
	}
	public List<String> getAllParamsInOrder() {
		// variety of ways of doing this operation
		return allParamsInOrder;
		//Set<String> allParams = new HashSet<String>();
		//for (String k: table.keySet()) {
		//	if (table.get(k).params != null) allParams.addAll(table.get(k).params);
		//}
		//return DashUtilFcns.setToList(allParams);
	}
	public void resolve(String root, EventTable et, VarTable vt, PredTable pt) {
		// resolve inits and invariants
		for (String sfqn: table.keySet()) {
			inits.addAll( 
				table.get(sfqn).origInits.stream()
					.map(i -> ResolveExpr.resolveExpr(this, et, vt, pt, "var", false, false, true, sfqn, i.getExp()))
					.collect(Collectors.toList()));
			invs.addAll(
				table.get(sfqn).origInvariants.stream()
					.map(i -> ResolveExpr.resolveExpr(this, et, vt, pt, "var", false, false, true, sfqn, i.getExp()))
					.collect(Collectors.toList()));
			// nothing to do for entered and exited
			// because they are resolved in context
		}
		isResolved = true;
	}


	public List<Expr> getInits() {
		return inits;
	}
	public List<Expr> getInvs() {
		return invs;
	}
	public List<Expr> getEnteredAction(String sfqn) {
		if (table.containsKey(sfqn))
			return table.get(sfqn).entered;  // could be null
		else { DashErrors.stateDoesNotExist("getEntered", sfqn); return null; }		
	}
	public List<Expr> getExitedAction(String sfqn) {
		if (table.containsKey(sfqn))
			return table.get(sfqn).exited;  // could be null
		else { DashErrors.stateDoesNotExist("getExited", sfqn); return null; }		
	}
	public boolean hasEnteredAction(String sfqn) {
		return (getEnteredAction(sfqn) == null);
	}
	public boolean hasExitedAction(String sfqn) {
		return (getExitedAction(sfqn) == null);
	}
	public List<DashRef> getLeafStatesExited(DashRef s) {
		List<DashRef> r = new ArrayList<DashRef>();
		//System.out.println("exiting" + s.toString());
		if (isLeaf(s.getName())) {
			r.add(s);
			return r;
		} else {
			// exit everything below even if not currently in it
			for (String ch:getImmChildren(s.getName())) {
				// exit all copies of the params
				List<Expr> newParamValues = new ArrayList<Expr>(s.getParamValues());
				if (hasParam(ch)) newParamValues.add(ExprHelper.createVar(getParam(ch)));
				r.addAll(getLeafStatesExited(DashRef.createStateDashRef(ch, newParamValues)));
			}
			return r;
		}
	}
	public List<String> getDefaults(String s) {
		if (!table.containsKey(s)) 
			{ DashErrors.stateDoesNotExist("getDefaults",s); return null; }
		// else if (isLeaf(s)) return null;
		else {
			assert(!isLeaf(s) || getImmChildren(s).isEmpty());
			return getImmChildren(s).stream()
  				.filter(c -> isDefault(c))
  				.collect(Collectors.toList());
  		}
	}
	public List<DashRef> getLeafStatesEntered(DashRef s) {
		List<DashRef> r = new ArrayList<DashRef>();
		if (isLeaf(s.getName())) 
			r.add(s);
		else {
			// enter every default below 
			// if enter one c/p state enter all
			// might be one (if o) or many (if c/p)
			List<String> defaults = getDefaults(s.getName());
			assert(defaults != null);
			for (String ch:defaults) {
				//System.out.println(ch);
				// enter all copies of the param if a parameterized state
				List<Expr> newParamValues = new ArrayList<Expr>(s.getParamValues());
				if (hasParam(ch))
					newParamValues.add(ExprHelper.createVar(getParam(ch)));
				r.addAll(getLeafStatesEntered(DashRef.createStateDashRef(ch, newParamValues)));
			}
		}
		return r;		
	}
	public List<DashRef> getRootLeafStatesEntered() {
		List<Expr> x = new ArrayList<Expr>();
		//System.out.println(getLeafStatesEntered(new DashRef(root,x)));
		return getLeafStatesEntered(DashRef.createStateDashRef(root,x));
	}
	public List<DashRef> allPrefixDashRefs(DashRef s) {
		List<String> allPrefixFQNs = DashFQN.allPrefixes(s.getName());
		List<DashRef> r = new ArrayList<DashRef>();
		int i = 0;
		for (String x:allPrefixFQNs) {
			if (isAnd(x) && hasParam(x)) {
				r.add(DashRef.createStateDashRef(x,s.getParamValues().subList(0,i+1)));
				i++;
			} else
				r.add(DashRef.createStateDashRef(x,s.getParamValues().subList(0,i)));
		}
		assert(i == s.getParamValues().size());
		return r;
	}
	/*
		Assumption: context is an ancestor of dest

		The param values of context do not have to match dest (but they will be subsets of the same set).
	
		The param values of context (from the scope) could be a set of param values or they could match dest
		(and therefore src of the trans as well). But they could be an ITE expression because of expressions
		used in src/dest.

		The dest param values must be singleton sets.
		Does not seem to be any room for syntactic simplifications in these expressions.
	*/
	
	public List<DashRef> getLeafStatesEnteredInScope(DashRef context, DashRef dest) {
		List<DashRef> cR = allPrefixDashRefs(context);
		List<DashRef> dR = allPrefixDashRefs(dest);
		//System.out.println("cR: "+cR);
		//System.out.println("dR: "+dR);
		// cR is a prefix of dR but possibly with different param values
		// enter all the possible side concurrent regions of the scope(context)
		List<DashRef> r = new ArrayList<DashRef>(); // result
		int p = 0; // parameter value position
		List<Expr> xP = new ArrayList<Expr>(); // parameters carrying forward
		List<Expr> nP; // parameters for each addition
		Expr e1;
		Expr e2;
		for (int i=0; i< cR.size(); i++) {
			DashRef c = cR.get(i);
			if (isAnd(c.getName()) && hasParam(c.getName())) {
				nP = new ArrayList<Expr>(xP);
				e1 = DashUtilFcns.lastElement(c.getParamValues());
				e2 = dest.getParamValues().get(p);
				if (!ExprHelper.sEquals(e1, e2)) {
					nP.add(ExprHelper.createDiff(e1,e2));
					r.addAll(getLeafStatesEntered(DashRef.createStateDashRef(c.getName(), nP)));
				} // if equal this is empty so don't include it
				xP.add(e2);  // just e2 for next one
				p++;
			}
		}
		//System.out.println("r: "+r);
		// we've dealt with all the side paths in cR of dR (including the last one in CR)
		// now deal with the rest of dR by looking at the side paths of the children
		// might be nothing in this loop if cR and dR are the same length
		for (int i=cR.size()-1;i< dR.size()-1;i++) {
			DashRef d = dR.get(i);  // first one will be match the last of cR
			DashRef chOfDest = dR.get(i+1);  
			//System.out.println("d: "+d);
			if (isAnd(chOfDest.getName())) {	
				// has sisters
				if (hasParam(chOfDest.getName())) {
					// ones not on path to dest
					nP = new ArrayList<Expr>
						(DashUtilFcns.allButLast(chOfDest.getParamValues()));
					// all param values
					e1 = ExprHelper.createVar(getParam(chOfDest.getName()));
					e2 = DashUtilFcns.lastElement(chOfDest.getParamValues());
					if (!ExprHelper.sEquals(e1, e2)) {
						nP.add(ExprHelper.createDiff(e1, e2));
						r.addAll(getLeafStatesEntered(
							DashRef.createStateDashRef(chOfDest.getName(),nP)));	
					} // if equal this is empty so don't include it		
				}
				//siblings
				List<String> children = getImmChildren(d.getName());
				List<String> andChildren = children.stream()
					.filter(c -> isAnd(c))
					.collect(Collectors.toList());
				andChildren.remove(chOfDest.getName());
				// siblings
				for (String ch:andChildren) {
					nP = new ArrayList<Expr>(d.getParamValues());
					if (hasParam(ch)) 
						// add the entire param set
						nP.add(ExprHelper.createVar(getParam(ch)));
					r.addAll(getLeafStatesEntered(DashRef.createStateDashRef(ch,nP)));		
				}		
			}
			// if its an OR state, just go on to the next one
		}
		//System.out.println("r "+r);
		r.addAll(getLeafStatesEntered(dest));
		return r;
	}


}