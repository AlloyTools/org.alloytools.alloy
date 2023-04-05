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
import static ca.uwaterloo.watform.core.DashUtilFcns.*;
import static ca.uwaterloo.watform.core.DashStrings.*;
import static ca.uwaterloo.watform.core.DashFQN.*;
import ca.uwaterloo.watform.alloyasthelper.ExprHelper;

import ca.uwaterloo.watform.ast.DashRef;

public class StateTable {
	private HashMap<String,StateElement> table;
	private boolean isResolved;
	private String root;

	private String space = " ";

	/* nested class for elementes in the state table */
	public class StateElement {
		// better than a tuple
		private DashStrings.StateKind kind; // must exist AND/OR
		private String param; // may be empty
		private List<String> params; // null if none; param is last of params if it exists
		private DashStrings.DefKind def; 
		// these all use fullQual names to point to trans in TransTable
		// or states in this StateTable
		private String parent; // null if none
		// this could be a set b/c there are no dups and order
		// doesn't matter, but lists are easier to work with
		private List<String> immChildren; // empty if none
		/*
		private ArrayList<String> transWithThisSrc;
		private ArrayList<String> transWithThisScope;
		// all trans with this scope or descendant scope
		private ArrayList<String> allTransWithinState; 
		private ArrayList<String> basicStatesEntered; // following defaults
		private ArrayList<String> basicStatesExited;
	    */

		public StateElement(
			DashStrings.StateKind k,
			String prm,
			List<String> prms, 
			DashStrings.DefKind d,
			String p, 
			List<String> iChildren) {
		
			assert(k != null);
			assert(prm == null || !prm.isEmpty());
			assert(prms != null);
			assert(p == null || !p.isEmpty());
			assert(iChildren != null); // could be empty
	
			this.kind = k; 
			this.param = prm;
			this.params = prms; 
			this.def = d; 
			this.parent = p; 
			this.immChildren = iChildren; 

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
		/*	
		this.substates = new ArrayList<DashState>();
		this.dynSymbols = new ArrayList<DashDecl>();
		this.events = new ArrayList<DashEvent>();
		this.transitions = new ArrayList<DashTrans>();
		this.init = new ArrayList<Expr>();
		this.invariants = new ArrayList<Expr>();
	
		for (Object i: items) {
			if (item instanceof DashState) {
				this.substates.add(i);
			} else if (item instanceof DashDecl) {
				this.dynSymbols.add(i);
			} else if (item instanceof DashEvent) {
				this.events.add(i);
			} else if (item instanceof DashTrans) {
				this.transitions.add(i);
			} else if (item instanceof DashInit) {
				this.inits.add(i);
			} else if (item instanceof DashInv) {
				this.invariants.add(i);
			} else {
				// error
			}
		}
		*/	
		/*
		public Boolean allAttributesEmpty() {
			return (kind == null && 
				param == null &&
				params == null &&
				def == null &&
				parent == null &&
			    immChildren.isEmpty() ) ;
		}
		*/
		public Boolean attributesSame(DashStrings.StateKind k, String prm, List<String> prms, DashStrings.DefKind d, String p, List<String> iChildren) {
			return (kind == k && 
				param.equals(prm) && 
				params.equals(prms) && 
				def.equals(d) && 
				parent.equals(p) && 
				immChildren.equals(iChildren));
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
		System.out.println("adding State table: "+fqn);
	}
	public void add(
		String fqn, 
		DashStrings.StateKind k, 
		String prm, 
		List<String> prms, 
		DashStrings.DefKind d,
		String p, 
		List<String> iChildren)  {
		// if its null, make it empty to not throw exceptions
		if (iChildren == null) iChildren = new ArrayList<String>();
		if (table.containsKey(fqn)) {
			StateElement se = table.get(fqn);
			if (se == null) 
				table.replace(fqn, new StateElement(k,prm, prms,d, p,iChildren));
			else if (!se.attributesSame(k,prm,prms,d,p,iChildren)) 
				// hopefully not possible
				DashErrors.addStateToStateTableDup(fqn);
		}
		else 
			table.put(fqn, new StateElement(k,prm, prms,d,p,iChildren));
		System.out.println("adding to State table: "+fqn+space+prm + space + prms+space+d+space+p+iChildren);
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

	public String getParam(String s) {
		if (table.containsKey(s))
			return table.get(s).param;  
		else { DashErrors.stateDoesNotExist("getParam", s); return null; }	
	}
	public List<String> getParams(String s) {
		if (table.containsKey(s))
			return table.get(s).params;  
		else { DashErrors.stateDoesNotExist("getParams", s); return null; }
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
	public String getClosestConcAnces(String s) {				
		// getAllAnces returns list from Root, ..., parentFQN on path
		// could also just walk back through parents
		List<String> allAnces = getAllAnces(s);
		//allAnces.add(s);
		Collections.reverse(allAnces);

		String concAnces = null;
		// allAnces cannot be empty b/c must have Root in it
		for (String a:allAnces) {
			if (isAnd(a) || isRoot(a)) {
				concAnces = a;
				break;
			}
		}
		//System.out.println("getClosestConcAnces: "+concAnces);
		return concAnces; // might be null
	}
	/*
	public List<String> getAllNonConcStatesWithinThisState(String concAnces) {		
		if (concAnces!=null) return getAllNonConcDesc(concAnces);
		else {
			// went back to root
			List <String> x = getAllNonConcDesc(root);
			//System.out.println("getAllNonConcStatesWithinThisState: "+x);
			return x;
		}
	}
	*/
	public List<String> getAllNonConcDesc(String s) {
		// get all the descendants not WITHIN concurrent states
		// s is included
		// have to be careful to avoid duplicates
		// System.out.println("getAllNonConcDesc "+s);
		List<String> desc = new ArrayList<String>();
		desc.add(s); // could be Root or a conc state
		//System.out.println("in getAllNonConcDesc: "+desc);
		if (table.containsKey(s)) {
			for (String c: table.get(s).immChildren) {
				//System.out.println("in getAllNonConcDesc: "+c);
				if (isOr(c)) desc.addAll(getAllNonConcDesc(c));
			}
			return desc;
		} else { DashErrors.stateDoesNotExist("getAllNonConcDesc", s); return null; }	
	}
	public List<String> getRegion(String sfqn) {
		return getAllNonConcDesc(getClosestConcAnces(sfqn));
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
	public List<String> getAllParams() {
		// variety of ways of doing this operation
		Set<String> allParams = new HashSet<String>();
		for (String k: table.keySet()) {
			if (table.get(k).params != null) allParams.addAll(table.get(k).params);
		}
		return DashUtilFcns.setToList(allParams);
	}
	public void resolveAll(String root) {
		System.out.println("Resolving state table");
		for (String k: table.keySet()) 
			if (table.get(k) == null) DashErrors.transUsesNonExistentState(k);
		// walk down parent to children and pass back info
		isResolved = true;
	}


	public List<DashRef> getLeafStatesExited(DashRef s) {
		List<DashRef> r = new ArrayList<DashRef>();
		System.out.println("exiting" + s.toString());
		if (isLeaf(s.getName())) {
			r.add(s);
			return r;
		} else {
			// exit everything below even if not currently in it
			for (String ch:getImmChildren(s.getName())) {
				// exit all copies of the params
				List<Expr> newParamValues = new ArrayList<Expr>(s.getParamValues());
				newParamValues.add(ExprHelper.createVar(getParam(ch)));
				r.addAll(getLeafStatesExited(new DashRef(ch, newParamValues)));
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
				// enter all copies of the param if a parameterized state
				List<Expr> newParamValues = new ArrayList<Expr>(s.getParamValues());
				newParamValues.add(ExprHelper.createVar(getParam(ch)));
				r.addAll(getLeafStatesEntered(new DashRef(ch, newParamValues)));
			}
		}
		return r;		
	}
	/*
		Assumption: context is an ancestor of dest
	*/
	public List<DashRef> getLeafStatesEnteredWithContext(DashRef context, DashRef dest) {
		List<DashRef> r = new ArrayList<DashRef>();
		if (context.getName().equals(dest.getName())) 
			r.addAll(getLeafStatesEntered(dest));
		else {
			// context must have children
			List<String> children = getImmChildren(context.getName());
			String chOfContext = DashFQN.getChildOfContextAncesOfDest(context.getName(),dest.getName());
			r.addAll(getLeafStatesEnteredWithContext(new DashRef(chOfContext,context.getParamValues()), dest));
			if (!isOr(chOfContext)) {
				// enter all sibling c/p's
				// treating c/p's the same
				List<String> andChildren = children.stream()
					.filter(c -> isAnd(c))
					.collect(Collectors.toList());
				andChildren.remove(chOfContext);
				for (String ch:children) {
					List<Expr> newParamValues = new ArrayList<Expr>();
					// if a c, won't be any additional params
					newParamValues.addAll(dest.getParamValues().subList(0, getParams(ch).size()-1));
					r.addAll(getLeafStatesEntered(new DashRef(ch, newParamValues)));
				}	
			}
		}
		return r;
	}
	/* seems like this goes in DashToAlloy
	public Expr createStateArrow(String s) {
		Expr e = createVar(s);
		for (i:s.params.reverse()) {
			e = createArrow(createVar(i),e);
		}
		return e;
	}
	*/

}
