/*  The StateTable maps:
	FullyQualStateName -> info about state

	It is created during the resolveAll phase.
*/

package ca.uwaterloo.watform.parser;

import java.io.*;


import java.util.HashMap;
import java.util.List;
import java.util.ArrayList;
import java.util.Collections;
import java.util.stream.Collectors;

import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprVar;

import ca.uwaterloo.watform.core.*;
import static ca.uwaterloo.watform.core.DashUtilFcns.*;
import ca.uwaterloo.watform.alloyasthelper.ExprHelper;
//import ca.uwaterloo.watform.alloyasthelper.ExprToString;
import ca.uwaterloo.watform.ast.*;

		// env events cannot be generated
		// env vars cannot be primed anywhere

public class TransTable {

	private HashMap<String,TransElement> table;
	private boolean isResolved;

	public class TransElement {
		public List<String> params; // null if no params
		public List<DashFrom> fromList;
		public List<DashOn> onList;
		public List<DashWhen> whenList;
		public List<DashGoto> gotoList;
		public List<DashSend> sendList;
		public List<DashDo> doList;



		// calculated when resolved
		public DashRef src; 
		public DashRef dest;
		public Expr when; // expr
		public DashRef on; // event
		public Expr act;
		public DashRef send;

		/*
		public List<DashDynSymbols> changedDynSymbols; // includes buffers
		*/
		public TransElement(
			List<String> prms,
			List<DashFrom> fl, 
			List<DashOn> ol,
			List<DashWhen> wl,
			List<DashGoto> gl,
			List<DashSend> sl,
			List<DashDo> dl
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
			this.fromList = fl;
			this.onList = ol;
			this.whenList = wl;
			this.gotoList = gl;
			this.sendList = sl;
			this.doList = dl;
		}
		public String toString() {
			String s = new String();
			s += "params: " + NoneStringIfNeeded(params) +"\n";
			s += "src: " + NoneStringIfNeeded(src) + "\n";
			s += "dest: " + NoneStringIfNeeded(dest) + "\n";
			s += "on: " + NoneStringIfNeeded(on) + "\n";
			s += "send: " + NoneStringIfNeeded(send) + "\n";
			s += "when: " + NoneStringIfNeeded(when) + "\n";
			s += "do: " + NoneStringIfNeeded(act) + "\n";
			// add more
			return s;
		}
		public void setSrc(DashRef s) {
			src = s;
		}
		public void setDest(DashRef d) {
			dest = d;
		}
		public void setOn(DashRef e) {
			on = e;
		}
		public void setSend(DashRef e) {
			send = e;
		}
		public void setWhen(Expr e) {
			when = e;
		}
		public void setDo(Expr e) {
			act = e;
		}
	}
	
	public TransTable() {
		table = new HashMap<String, TransElement>();
		isResolved = false;
	}
	public boolean add(
			String tfqn,
			List<String> params,
			List<DashFrom> fromList,
			List<DashOn> onList,
			List<DashWhen> whenList,
			List<DashGoto> gotoList,
			List<DashSend> sendList,
			List<DashDo> doList
		)
	{
		//System.out.println("Adding "+tfqn);
		//System.out.println("onList: " + NoneStringIfNeeded(onList));
		assert(!tfqn.isEmpty());
		assert(params != null );
		assert(fromList != null);
		assert(onList != null);
		assert(whenList != null);
		assert(gotoList != null);
		assert(sendList != null);
		assert(doList != null);
		if (table.containsKey(tfqn)) return false;
		else if (DashStrings.hasPrime(tfqn)) { DashErrors.nameShouldNotBePrimed(tfqn); return false; }
		else { table.put(tfqn, new TransElement(params,fromList,onList,whenList,gotoList,sendList,doList)); return true; }
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

	public List<String> getAllTransNames() {
		return new ArrayList<String>(table.keySet());
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
	public DashRef getOn(String t) {
		if (table.containsKey(t)) return table.get(t).on;
		else { DashErrors.transDoesNotExist("getOn", t); return null; }
	}
	public DashRef getSend(String t) {
		if (table.containsKey(t)) return table.get(t).send;
		else { DashErrors.transDoesNotExist("getSend", t); return null; }
	}
	public Expr getDo(String t) {
		if (table.containsKey(t)) return table.get(t).act;
		else { DashErrors.transDoesNotExist("getDo", t); return null; }
	}
	public Expr getWhen(String t) {
		if (table.containsKey(t)) return table.get(t).when;
		else { DashErrors.transDoesNotExist("getWhen", t); return null; }
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
	 * check for errors and put all the trans that are at this level
	 * in the trans table
	 * must be done after resolveAllState
	 * this fcn does not modify anything in this object
	 */
	public void resolve(StateTable st, EventTable et, VarTable vt) {

		//System.out.println(st);
		//System.out.println(toString());
		//System.out.println("Resolving trans table");
		if (getAllTransNames().isEmpty()) DashErrors.noTrans();
		for (String tfqn: table.keySet()) {
			//String tfqn = DashFQN.fqn(sfqn,t.name);
			String parentFQN = DashFQN.chopPrefixFromFQN(tfqn);
			// determining the src state
			List<DashRef> fList =
				table.get(tfqn).fromList.stream()
				.map(p -> (p.src))
				.collect(Collectors.toList());

			if (fList.size() > 1) DashErrors.tooMany("from", tfqn);
			else if (fList.isEmpty()) 
				// can be a loop on root
				table.get(tfqn)
					.setSrc(new DashRef(parentFQN, ExprHelper.createVarList(DashStrings.pName,getParams(tfqn))));
			else 
				table.get(tfqn)
					.setSrc(
						st.resolveSrcDest("from", 
							fList.get(0), 
							tfqn,
							getParams(tfqn), 
							vt));
	
			// determining the dest state
			List<DashRef> gList =
				table.get(tfqn).gotoList.stream()
				.map(p -> (p.dest))
				.collect(Collectors.toList());

			if (gList.size() > 1) DashErrors.tooMany("goto", tfqn);
			else if (gList.isEmpty()) 
				// can be a loop on root
				table.get(tfqn)
					.setDest(new DashRef(parentFQN, ExprHelper.createVarList(DashStrings.pName,getParams(tfqn))));
			else 
				table.get(tfqn)
					.setDest(
						st.resolveSrcDest("goto", 
							gList.get(0), 
							tfqn,
							getParams(tfqn), 
							vt));

			// determining the on (event)
			List<Expr> onExpList =
				table.get(tfqn).onList.stream()
				.map(p -> (p.getExp()))
				.collect(Collectors.toList());
			if (onExpList.size() > 1) DashErrors.tooMany("on", tfqn);
			else if (!onExpList.isEmpty()) {
				table.get(tfqn)
					.setOn(
						et.resolveEvent("on", 
							onExpList.get(0), 
							st.getRegion(DashFQN.chopPrefixFromFQN(tfqn)), 
							tfqn, 
							getParams(tfqn),
							vt));
			}

			// determining the send
			List<Expr> sendExpList =
				table.get(tfqn).sendList.stream()
				.map(p -> (p.getExp()))
				.collect(Collectors.toList());
			if (sendExpList.size() > 1) DashErrors.tooMany("send", tfqn);
			else if (!sendExpList.isEmpty()) {
				table.get(tfqn)
					.setSend(
						et.resolveEvent("send", 
							sendExpList.get(0),
							st.getRegion(DashFQN.chopPrefixFromFQN(tfqn)), 
							tfqn, 
							getParams(tfqn), 
							vt));
			}

			// determining the when (expr)
			List<Expr> whenExpList =
				table.get(tfqn).whenList.stream()
				.map(p -> (p.getWhen()))
				.collect(Collectors.toList());
			if (whenExpList.size() > 1) DashErrors.tooMany("when", tfqn);
			else if (!whenExpList.isEmpty()) {
				table.get(tfqn)
					.setWhen(
						vt.resolveExpr("when", 
							whenExpList.get(0), 
							st.getRegion(DashFQN.chopPrefixFromFQN(tfqn)), 
							tfqn, 
							getParams(tfqn)));
			}

			// determining the do
			List<Expr> doExpList =
				table.get(tfqn).doList.stream()
				.map(p -> (p.getDo()))
				.collect(Collectors.toList());
			if (doExpList.size() > 1) DashErrors.tooMany("on", tfqn);
			else if (!doExpList.isEmpty()) {
				table.get(tfqn)
					.setDo(
						vt.resolveExpr("do", doExpList.get(0), 
							st.getRegion(DashFQN.chopPrefixFromFQN(tfqn)), 
							tfqn, 
							getParams(tfqn)));
			}

		}
		isResolved = true;
	}





    // [n1,n2,...]
    /*private List<Expr> paramVars(List<String> names) {
        List<Expr> o = new ArrayList<Expr>();
        for (String n: names) o.add(ExprHelper.createVar(DashStrings.pName+n));
        return o;
    }*/




	public boolean[] transAtThisParamDepth(int max) {
		boolean[] depthsInUse = new boolean[max+1]; // 0..max
		for (int i=0; i <= max; i++) depthsInUse[i] = false;
		for (String k:table.keySet()) 
			if (table.get(k).params == null) depthsInUse[0] = true;
			else depthsInUse[table.get(k).params.size()] = true;
		return depthsInUse;
	}

}
