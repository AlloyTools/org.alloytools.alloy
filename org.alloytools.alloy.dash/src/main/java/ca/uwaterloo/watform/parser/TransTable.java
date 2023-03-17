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
import ca.uwaterloo.watform.ast.*;

public class TransTable {

	private HashMap<String,TransElement> table;
	private boolean isResolved;

	public class TransElement {
		public List<String> params; // null if no params
		public String src; // FQN
		public String dest; // FQN
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
			String s, // fqn
			String d // fqn
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
			s += "params: "+params +"\n";
			s += "src: "+src +"\n";
			s += "dest: "+dest +"\n";
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
			String s,
			String d)
	/*
			DashEvent w,
			DashExpr o,
			List<DashExpr> a,
			List<DashEvent> se) {
	*/
	{
		System.out.println("Adding "+fqn);
		assert(!fqn.isEmpty());
		assert(params == null | !params.isEmpty());
		assert(!s.isEmpty());
		assert(!d.isEmpty());
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
	public void resolveAll() {
		System.out.println("Resolving trans table");
		if (getTransNames().isEmpty()) DashErrors.noTrans();
		// check all source and dest exist in state table
		isResolved = true;
	}

}
