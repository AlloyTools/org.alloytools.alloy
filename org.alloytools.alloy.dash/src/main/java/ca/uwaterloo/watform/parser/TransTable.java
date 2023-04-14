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

import edu.mit.csail.sdg.ast.Expr;

import ca.uwaterloo.watform.core.*;
import static ca.uwaterloo.watform.core.DashUtilFcns.*;
import ca.uwaterloo.watform.alloyasthelper.ExprHelper;
import ca.uwaterloo.watform.ast.*;

public class TransTable {

	private HashMap<String,TransElement> table;
	private boolean isResolved;

	public class TransElement {
		public List<String> params; // null if no params
		public DashRef src; 
		public DashRef dest;
		public Expr when; // just one?
		public Expr on;
		public List<Expr> action;
		public List<Expr> send;

		/*
		public List<DashDynSymbols> changedDynSymbols; // includes buffers

		// don't need scope - it is calculated from FQNs
		public Set<String> higherPriority;
		public Set<String> orthogonal; // keep both lists just in case
		public Set<String> notOrthogonal; 
		public Set<String> changedDynSymbols;
		*/
		public TransElement(
			List<String> prms,
			DashRef s, 
			DashRef d 
		)
		/*
			DashEvent w,
			DashExpr o,
			List<DashExpr> a,
			List<DashEvent> s
			) 
		*/
		{
			this.params = prms;
			this.src = s;
			this.dest = d;
			/*
			this.when = w;
			this.on = o;
			this.action = a;
			this.send = s;
			this.changedDynSymbols = null; // not yet known; consists of FQN list
			this.higherPriorityTrans = null; // not yet known; FQNs
			this.notOrthogonal = null; // not yet known; FQNs
			this.orthogonal =  null;
			this.basicStatesEntered = null;
			this.basicStatesExited = null;
			*/
		}
		public String toString() {
			String s = new String();
			s += "params: " + params +"\n";
			s += "src: " + src.toString() + "\n";
			s += "dest: " + dest.toString() + "\n";
			// add more
			return s;
		}
	}
	
	public TransTable() {
		table = new HashMap<String, TransElement>();
		isResolved = false;
	}
	public void add(
			String fqn,
			List<String> params,
			DashRef s,
			DashRef d)
	/*
			DashEvent w,
			DashExpr o,
			List<DashExpr> a,
			List<DashEvent> se) {
	*/
	{
		System.out.println("Adding "+fqn);
		assert(!fqn.isEmpty());
		assert(params != null );
		assert(s != null);
		assert(d != null);
		if (table.containsKey(fqn)) DashErrors.transTableDup(fqn);
		else table.put(fqn, new TransElement(params,s,d));
	}
	public String toString() {
		String s = new String();
		s += "TRANS TABLE\n";
		for (String k:table.keySet()) {
			s += " ----- \n";
			s += k + "\n";
			s += table.get(k).toString();
		}
		return s;
	}
	public Set<String> getTransNames() {
		return table.keySet();
	}
	public List<String> getParams(String t) {
		if (table.containsKey(t)) return table.get(t).params;
		else { DashErrors.transDoesNotExist("getParams", t); return null; }
	}
	public DashRef getSrc(String t) {
		if (table.containsKey(t)) return table.get(t).src;
		else { DashErrors.transDoesNotExist("getSrc", t); return null; }
	}
	public DashRef getDest(String t) {
		if (table.containsKey(t)) return table.get(t).dest;
		else { DashErrors.transDoesNotExist("getDest", t); return null; }
	}
	// might be better to make this getTransWithThisSrc
	// but this is more efficient if it is only used for higherPriTrans
	public List<String> getTransWithTheseSrcs(List<String> slist) {
		List<String> tlist = new ArrayList<String>();
		for (String k:table.keySet()) {
			if (slist.contains(table.get(k).src.getName())) tlist.add(k);
		}
		return tlist;
	}
	public List<String> getHigherPriTrans(String t) {
		// list returned could be empty
		List<String> tlist = new ArrayList<String>();
		// have to look for transitions from sources earlier on the path of this transitions src
		List<String> allPrefixes = DashFQN.allPrefixes(table.get(t).src.getName());
		// remove the src state itself
		allPrefixes.remove(allPrefixes.size()-1);
		if (table.containsKey(t)) tlist.addAll(getTransWithTheseSrcs(allPrefixes)); 
		else  DashErrors.transDoesNotExist("getParams", t); 
		return tlist;
	}



	/*
	public List<String> getNotOrthogonalTransAbove(String t) {
		List<String> notOrthogonal = new ArrayList<String>();
		String tScope = getScope(table.get(t).src, table.get(t).dest);
		// get scope of this trans
		for (to: table.getKeys()) {
			if (!t.equals(to)) {
				String toScope = getScope(table.get(to).src, table.get(to).dest);
				if (!isBelow(toScope, tScope)) {
					// will be caught by !takeni's below this trans
					;
				} else if (isBelow(tScope, toScope)) {
					notOrthogonal.add(to);
				} else {
					
				}

			}
		}
			get scope of to
			get lca of 
	}
	*/
	public void resolveAll() {
		System.out.println("Resolving trans table");
		if (getTransNames().isEmpty()) DashErrors.noTrans();
		isResolved = true;
	}
	public boolean[] transAtThisParamDepth(int max) {
		boolean[] depthsInUse = new boolean[max+1]; // 0..max
		for (int i=0; i <= max; i++) depthsInUse[i] = false;
		for (String k:table.keySet()) 
			if (table.get(k).params == null) depthsInUse[0] = true;
			else depthsInUse[table.get(k).params.size()] = true;
		return depthsInUse;
	}

}
