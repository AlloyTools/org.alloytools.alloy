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

import ca.uwaterloo.watform.core.*;

public class StateTable {
	private HashMap<String,StateElement> table;
	private boolean isResolved;
	private String root;

	private String space = " ";

	/* nested class for elementes in the state table */
	public class StateElement {
		// better than a tuple
		private DashStrings.StateKind kind; // must exist AND/OR
		private List<String> params; // null if none
		private String def; // null if none
		// these all use fullQual names to point to trans in TransTable
		// or states in this StateTable
		private String parent; // null if none
		// this could be a set b/c there are no dups and order
		// doesn't matter, but lists are easier to work with
		private List<String> immChildren; // empty if none
		private ArrayList<String> transWithThisSrc;
		private ArrayList<String> transWithThisScope;
		// all trans with this scope or descendant scope
		private ArrayList<String> allTransWithinState; 
		private ArrayList<String> basicStatesEntered; // following defaults
		private ArrayList<String> basicStatesExited;


		public StateElement(
			DashStrings.StateKind k,
			List<String> prms, 
			String d,
			String p, 
			List<String> iChildren) {
			assert(k != null);
			assert(prms == null || !prms.isEmpty());
			assert(def == null || !def.isEmpty());
			assert(parent == null || !parent.isEmpty());
			assert(immChildren != null); // could be empty
			this.kind = k; 
			this.params = prms; 
			this.def = d; 
			this.parent = p; 
			this.immChildren = iChildren; 
			this.transWithThisSrc = null;
			this.transWithThisScope = null;
			this.allTransWithinState = null;
			this.basicStatesEntered = null;
			this.basicStatesExited = null;
		}
		public String toString() {
			String s = new String();
			s += "kind: "+kind +"\n";
			s += "params: "+params +"\n";
			s += "default: "+def+"\n";
			s += "parent: "+parent +"\n";
			s += "immChildren: "+immChildren +"\n";
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
		public Boolean allAttributesEmpty() {
			return (kind == null || 
				params == null ||
				def == null || 
				parent == null ||
			    immChildren == null ||
			    transWithThisSrc == null ||
			    transWithThisScope == null ||
			    allTransWithinState == null ||
			    basicStatesEntered == null ||
			    basicStatesExited == null);
		}
		public Boolean attributesSame(DashStrings.StateKind k,List<String> prms, String d, String p, List<String> iChildren) {
			return (kind == k && 
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
		// System.out.println("adding State table: "+fqn);
	}
	public void add(
		String fqn, 
		DashStrings.StateKind k, 
		List<String> prms, 
		String d,
		String p, 
		List<String> iChildren)  {
		// if its null, make it empty to not throw exceptions
		if (iChildren == null) iChildren = new ArrayList<String>();
		if (table.containsKey(fqn)) {
			StateElement se = table.get(fqn);
			if (se.allAttributesEmpty()) 
				table.replace(fqn, new StateElement(k,prms,d, p,iChildren));
			else if (!se.attributesSame(k,prms,d,p,iChildren)) 
				// hopefully not possible
				DashErrors.addStateToStateTableDup(fqn);
		}
		else 
			table.put(fqn, new StateElement(k,prms,d,p,iChildren));
		System.out.println("adding to State table: "+fqn+space+prms+space+d+space+p+iChildren);
	}
	
	public boolean containsKey(String q) {
		return table.containsKey(q);
	}
	public boolean isBasicState(String q)  {
		if (table.containsKey(q)) 
			// shouldn't really need the check for OR here
			return (table.get(q).kind == DashStrings.StateKind.OR && table.get(q).immChildren == null);
		else { DashErrors.isBasicNotExist(q); return false; }
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
		// don't want to include the state itself
		if (fqnSplit.size()-1 > 0) for (int i=0; i < fqnSplit.size()-1; i++) x.add(DashFQN.fqn(fqnSplit.subList(0,i+1)));
		// list is in order from root, ...., fqn-1 on path
		return x;
	}
	public String getClosestConcAnces(String s) {				
		// getAllAnces returns list from Root, ..., parentFQN-1 on path
		// could also just walk back through parents
		List<String> allAnces = getAllAnces(s);
		allAnces.add(s);
		Collections.reverse(allAnces);

		String concAnces = null;
		// allAnces cannot be empty b/c must have Root in it
		for (String a:allAnces) {
			if (getKind(a) == DashStrings.StateKind.AND) {
				concAnces = a;
				break;
			}
		}
		return concAnces; // might be null
	}
	public List<String> getAllNonConcStatesWithinThisState(String concAnces) {		
		if (concAnces!=null) return getAllNonConcDesc(concAnces);
		else 
			// went back to root
			return getAllNonConcDesc(root);
	}

	public List<String> getAllNonConcDesc(String s) {
		// get all the descendants not in concurrent states
		// s is not included
		System.out.println("getAllNonConcDesc "+s);
		List<String> desc = new ArrayList<String>();
		if (table.containsKey(s)) {
			if (!table.get(s).immChildren.isEmpty()) {
				System.out.println("HERE " + table.get(s).immChildren);
				if (table.get(table.get(s).immChildren.get(0)).kind != DashStrings.StateKind.AND) {
					for (String c: table.get(s).immChildren) {
						desc.addAll(getAllNonConcDesc(c));
						desc.add(c);
					}
					return desc;
				} else return desc; // empty list
			} else return desc; // empty list
		}  
		else { DashErrors.stateDoesNotExist("getAllNonConcDesc", s); return null; }	
	}
	public DashStrings.StateKind getKind(String s) {
		if (table.containsKey(s))
			return table.get(s).kind; 
		else { DashErrors.stateDoesNotExist("getKind", s); return null; }		
	}
	public int getMaxDepthParams() {
		return getMaxDepthParams(root);
	}
	public int getMaxDepthParams(String s) {
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
	/*
	public void addEnterExit(String s, ArrayList<String> enter, ArrayList<String> exit) {
		if (s in table.keys()) {
			table.get(s).basicStatesEntered = enter;
			table.get(s).basicStatesExited = exit;
		} else {
			// error
		}
	}
	public ArrayList<String> getParams(String s) {
		assert(isResolved == true);
		return table.get(s).params;
	}
	public ArrayList<String> getBasicStatesEntered(String s) {
		assert(isResolved == true);
		return table.get(s).basicStatesEntered;
	}
	public ArrayList<String> getBasicStatesExited(String s) {
		assert(isResolved == true);
		return table.get(s).basicStatesExited;
	}
	public Expr createStateArrow(String s) {
		Expr e = createVar(s);
		for (i:s.params.reverse()) {
			e = createArrow(createVar(i),e);
		}
		return e;
	}

	*/

}
