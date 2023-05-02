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
		public Expr when; // just one?
		public DashRef on;
		public List<Expr> action;
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

	public Set<String> getAllTransNames() {
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
	public DashRef getOn(String t) {
		if (table.containsKey(t)) return table.get(t).on;
		else { DashErrors.transDoesNotExist("getOn", t); return null; }
	}
	public DashRef getSend(String t) {
		if (table.containsKey(t)) return table.get(t).send;
		else { DashErrors.transDoesNotExist("getSend", t); return null; }
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
	public void resolve(StateTable st, EventTable et) {

		//System.out.println(st);
		//System.out.println(toString());
		//System.out.println("Resolving trans table");
		if (getAllTransNames().isEmpty()) DashErrors.noTrans();
		for (String tfqn: table.keySet()) {
			//String tfqn = DashFQN.fqn(sfqn,t.name);

			// determining the src state
			List<DashRef> fList =
				table.get(tfqn).fromList.stream()
				.map(p -> (p.src))
				.collect(Collectors.toList());
			table.get(tfqn).setSrc(determineSrcDest("from", fList, st, tfqn));
	
			// determining the dest state
			List<DashRef> gList =
				table.get(tfqn).gotoList.stream()
				.map(p -> (p.dest))
				.collect(Collectors.toList());
			table.get(tfqn).setDest(determineSrcDest("goto", gList, st, tfqn));

			// determining the when



			// determining the on
			List<Expr> onExpList =
				table.get(tfqn).onList.stream()
				.map(p -> (p.getExp()))
				.collect(Collectors.toList());
			table.get(tfqn).setOn(determineEvent("on", onExpList,st, et, tfqn));

			// determining the send
			List<Expr> sendExpList =
				table.get(tfqn).sendList.stream()
				.map(p -> (p.getExp()))
				.collect(Collectors.toList());
			table.get(tfqn).setSend(determineEvent("send", sendExpList,st, et, tfqn));

			// determining the do

		}
		isResolved = true;
	}

	/*
	 * this fcn figures out the src/dest of a transition
	 * from its context
	 * if it has no src/dest, the parent state is used
	 * if it is already FQN, it is returned directly
	 * Otherwise, it looks at all uniquely named states up to an ancestor conc state
	 * Requires state table to have been built already
	 */
 
	public DashRef determineSrcDest(String xType, List<DashRef> ll,  StateTable st, String tfqn) {

		// parent state of this transition
		String parentFQN = DashFQN.chopPrefixFromFQN(tfqn);
		if (ll.size() > 1) {
			DashErrors.moreThanOneSrcDest(xType, tfqn);
			return null;
		} else if (ll.isEmpty()) 
			// can be a loop on root
			return new DashRef(parentFQN, ExprHelper.createVarList(DashStrings.pName,st.getParams(parentFQN)));
		else {
			// if has slashes, turn to "-"
			DashRef x = ll.get(0);
			//System.out.println("Looking for: " + x);
			String n = DashFQN.fqn(x.getName());
			if (DashFQN.isFQN(n)) {
				// number of params provided must match number of params needed
				//System.out.println(x.getParamValues().size());
				//System.out.println(st.getParams(x.getName()).size());
				if (x.getParamValues().size() != st.getParams(n).size()) {
					DashErrors.fqnSrcDestMustHaveRightNumberParams(xType,tfqn);
					return null;
				}
				if (!st.containsKey(n)) DashErrors.unknownSrcDest(x.getName(),xType,tfqn);
				return x;
			} else {
				// not fully qualified
				// shouldn't have params in DashRef
				// Root could be here but won't have params 
				if (!x.getParamValues().isEmpty()) {
					DashErrors.srcDestCantHaveParam(xType,tfqn);
					return null;
				}
				// Root ends up here
				List<String> matches = new ArrayList<String>();
				//String a = st.getClosestConcAnces(parentFQN);
				//System.out.println("getClosestConcAnces: "+a);
				//List<String> b = st.getAllNonConcStatesWithinThisState(a);
				//System.out.println("getAllNonConcStatesWithinThisState "+b);
				for (String s:st.getRegion(parentFQN)) {
					//System.out.println(s + " " + n);
					if (DashFQN.suffix(s,n)) matches.add(s);
				}
				//System.out.println("matches: " + matches);
				if (matches.size() > 1) {
					DashErrors.ambiguousSrcDest(xType, tfqn);
					return null; 
				} else if (matches.isEmpty()) {
					//DashUtilFcns.myprint(st.toString());
					DashErrors.unknownSrcDest(x.getName(),xType,tfqn);
					return null;
				} else {
					String m = matches.get(0);
					//System.out.println(m);
					// must have same param values as trans b/c in same conc region
					return new DashRef(m, ExprHelper.createVarList(DashStrings.pName, st.getParams(m)));
				}
			}
		}
	}

    // [n1,n2,...]
    /*private List<Expr> paramVars(List<String> names) {
        List<Expr> o = new ArrayList<Expr>();
        for (String n: names) o.add(ExprHelper.createVar(DashStrings.pName+n));
        return o;
    }*/

	private DashRef determineEvent(String xType, List<Expr> expList, StateTable st, EventTable et, String tfqn) {
		if (expList.isEmpty()) return null;
		else if (expList.size() > 1) {
			DashErrors.tooManyEvents(xType, tfqn);
			return null;
		} else {
			Expr exp = expList.get(0);
			// don't include isDashRefJoin here because that is only possible for actions not events
			// which are tuples
			// but a DashRefProcessRef could be either a value for an action
			// or a tuple for an event
			// Arrow: b1 -> a1 -> ev
			// ProcessRef: A/B/C[a1,b1]/ev which became $$PROCESSREF$$. b1.a1.A/B/C/ev in parsing
			// BadJoin: ev[a1,b1] which became b1.a1.ev in parsing 
			if (ExprHelper.isExprVar(exp) ||
				DashRef.isDashRefArrow(exp) || 
				DashRef.isDashRefProcessRef(exp) || 
				DashRef.isDashRefBadJoin(exp)) {
				String e;
				List<Expr> paramValues;
				if (ExprHelper.isExprVar(exp)) {
					e = ExprHelper.getVarName((ExprVar) exp);	
					paramValues = new ArrayList<Expr>();
				} else {
					e = DashFQN.fqn(DashRef.nameOfDashRefExpr(exp));
					paramValues = DashRef.paramValuesOfDashRefExpr(exp);
				}
				String efqn = DashFQN.fqn(e);
				String parentFQN = DashFQN.chopPrefixFromFQN(tfqn);
				//System.out.println(efqn);
				List<String> matches = new ArrayList<String>();
				for (String s:st.getRegion(parentFQN)) 
					for (String x:et.allEventsOfState(s)) {
						//System.out.println(x);
						if (DashFQN.suffix(x,efqn)) matches.add(x);
					}
				if (matches.size() > 1) {
					DashErrors.ambiguousEvent(xType, e, tfqn);
					return null; 
				} else if (matches.isEmpty()) {
					DashErrors.unknownEvent(xType, e,tfqn);
					return null;
				} else {
					String m = matches.get(0);	
					if (paramValues.isEmpty()) {
						// must have same param values as trans b/c in same conc region
						if (et.getParams(m).size() > getParams(tfqn).size()) {
							// getRegion did not return things that all
							// have the same parameter values
							DashErrors.regionMatchesWrongParamNumber();
							return null;
						} else {
							// but could be a subset of transition param values
							List<Expr> prmValues = 
								ExprHelper.createVarList(DashStrings.pName,
									getParams(tfqn).subList(0, et.getParams(m).size() ));
							return new DashRef(m, prmValues);							
						}
					} else if (et.getParams(m).size() != paramValues.size()) { 
						// came with parameters so must be right number
						DashErrors.fqnEventMissingParameters(xType, e, tfqn); 
						return null;
					} else {
						return new DashRef(efqn, paramValues);
					}
				}
			} else {
				DashErrors.expNotEvent(xType, tfqn);
				return null;
			}
		}
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
