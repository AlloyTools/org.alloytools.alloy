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
import ca.uwaterloo.watform.dashtoalloy.Common;
import static ca.uwaterloo.watform.parser.ResolveExpr.*;



public class TransTable implements Serializable {

	private HashMap<String,TransElement> table;
	private boolean isResolved;

	public class TransElement {
		public List<String> params; // null if no params
		public List<Integer> paramsIdx;
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
			List<Integer> prmsIdx,
			List<DashFrom> fl, 
			List<DashOn> ol,
			List<DashWhen> wl,
			List<DashGoto> gl,
			List<DashSend> sl,
			List<DashDo> dl
		)
		{
			this.params = prms;
			this.paramsIdx = prmsIdx;
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
			s += "paramsIdx: " + NoneStringIfNeeded(paramsIdx) +"\n";
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
			List<Integer> paramsIdx,
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
		assert(paramsIdx != null);
		assert(fromList != null);
		assert(onList != null);
		assert(whenList != null);
		assert(gotoList != null);
		assert(sendList != null);
		assert(doList != null);
		if (table.containsKey(tfqn)) return false;
		else if (DashStrings.hasPrime(tfqn)) { DashErrors.nameShouldNotBePrimed(tfqn); return false; }
		else { table.put(tfqn, new TransElement(params,paramsIdx, fromList,onList,whenList,gotoList,sendList,doList)); return true; }
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
	public List<Integer> getParamsIdx(String t) {
		if (table.containsKey(t)) return table.get(t).paramsIdx;
		else { DashErrors.transDoesNotExist("getParamsIdx", t); return null; }
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
		String src = table.get(t).src.getName();
		List<String> tlist = new ArrayList<String>();
		// have to look for transitions from sources earlier on the path of this transitions src
		// allPrefixes includes t so it contains at least one item
		List<String> allPrefixes = DashFQN.allPrefixes(src);
		// remove the src state itself
		allPrefixes.remove(src);
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
	public void resolve(StateTable st, EventTable et, VarTable vt, PredTable pt) {

		//System.out.println(st);
		//System.out.println(toString());
		//System.out.println("Resolving trans table");
		if (getAllTransNames().isEmpty()) DashErrors.noTrans();
		for (String tfqn: table.keySet()) {
			//String tfqn = DashFQN.fqn(sfqn,t.name);
			String sfqn = DashFQN.chopPrefixFromFQN(tfqn);
			// determining the src state
			List<Expr> fList =
				table.get(tfqn).fromList.stream()
				.map(p -> (p.src))
				.collect(Collectors.toList());

			if (fList.size() > 1) DashErrors.tooMany("from", tfqn);
			else if (fList.isEmpty()) 
				// can be a loop on root
				table.get(tfqn)
					.setSrc(DashRef.createStateDashRef(sfqn, 
								Common.paramVars(getParamsIdx(tfqn), getParams(tfqn))));
			else 
				table.get(tfqn)
					.setSrc((DashRef) resolveExpr(st, et, vt, pt, "state", false, false, true, sfqn, fList.get(0)));
	
			// determining the dest state
			List<Expr> gList =
				table.get(tfqn).gotoList.stream()
				.map(p -> (p.dest))
				.collect(Collectors.toList());

			if (gList.size() > 1) DashErrors.tooMany("goto", tfqn);
			else if (gList.isEmpty()) 
				// can be a loop on root
				table.get(tfqn)
					.setDest(DashRef.createStateDashRef(sfqn, 
								Common.paramVars(getParamsIdx(tfqn),getParams(tfqn))));
			else 
				table.get(tfqn)
					.setDest((DashRef) resolveExpr(st, et, vt, pt, "state", false, true, true, sfqn, gList.get(0)));

			// determining the on (event)
			List<Expr> onExpList =
				table.get(tfqn).onList.stream()
				.map(p -> (p.getExp()))
				.collect(Collectors.toList());
			if (onExpList.size() > 1) DashErrors.tooMany("on", tfqn);
			else if (!onExpList.isEmpty()) {
				table.get(tfqn)
					.setOn((DashRef) resolveExpr(st, et, vt, pt, "event", false, false, true, sfqn, onExpList.get(0)));
			}

			// determining the send
			List<Expr> sendExpList =
				table.get(tfqn).sendList.stream()
				.map(p -> (p.getExp()))
				.collect(Collectors.toList());
			if (sendExpList.size() > 1) DashErrors.tooMany("send", tfqn);
			else if (!sendExpList.isEmpty()) {
				DashRef x = (DashRef) resolveExpr(st, et, vt, pt, "event", false, true, true, sfqn, sendExpList.get(0));
				if (et.isEnvironmentalEvent(x.getName()))
					DashErrors.cantSendAnEnvEvent(sendExpList.get(0).pos(),sendExpList.get(0).toString());
				else
					table.get(tfqn)
					.	setSend((DashRef) resolveExpr(st, et, vt, pt, "event", false, true, true, sfqn, sendExpList.get(0)));
			}

			// determining the when (expr)
			List<Expr> whenExpList =
				table.get(tfqn).whenList.stream()
				.map(p -> (p.getWhen()))
				.collect(Collectors.toList());
			if (whenExpList.size() > 1) DashErrors.tooMany("when", tfqn);
			else if (!whenExpList.isEmpty()) {
				table.get(tfqn)
					.setWhen(resolveExpr(st, et, vt, pt, "var", false, false, true, sfqn, whenExpList.get(0)));
			}

			// determining the do
			List<Expr> doExpList =
				table.get(tfqn).doList.stream()
				.map(p -> (p.getDo()))
				.collect(Collectors.toList());
			if (doExpList.size() > 1) DashErrors.tooMany("on", tfqn);
			else if (!doExpList.isEmpty()) {
				// already resolved src/dest
				Expr action = doExpList.get(0);
				if (st.hasEnteredAction(getDest(tfqn).getName()))
					action = ExprHelper.createAnd(action,ExprHelper.createAndList(st.getEnteredAction(getDest(tfqn).getName())));
				if (st.hasExitedAction(getSrc(tfqn).getName()))
					action = ExprHelper.createAnd(action,ExprHelper.createAndList(st.getExitedAction(getSrc(tfqn).getName())));
				table.get(tfqn)
					.setDo(resolveExpr(st, et, vt, pt, "var", true, true, true, sfqn, action));
			}

		}

		// these are conservative measures of potential problems in the model

		// we check that every internal event is generated by some transitions
		// if not, may end up with some untriggerable transitions
		// there is no resolveEvents so this can be done here

		// we could limit this to int events that trigger something 
		// but it seems wrong to put in an unused internal event so we will flag it also

		List<String> intEventsGenerated = getAllTransNames().stream()
			.filter(i -> getSend(i)!=null)
			.map(i -> getSend(i).getName())
			.collect(Collectors.toList());
		List<String> intEventsNotGenerated = 
			et.getAllInternalEvents().stream()
			.filter(i -> !(intEventsGenerated.contains(i)))
			.collect(Collectors.toList());
		if (!intEventsNotGenerated.isEmpty())
			DashErrors.intEventsNotGenerated(intEventsNotGenerated);

		// we check that every external event is the trigger of some transition
		List<String> eventsThatTriggerTrans = getAllTransNames().stream()
			.filter(i -> getOn(i)!=null)
			.map(i -> getOn(i).getName())
			.collect(Collectors.toList());
		List<String> envEventsNotUsed = 
			et.getAllEnvironmentalEvents().stream()
			.filter(i -> !(eventsThatTriggerTrans.contains(i)))
			.collect(Collectors.toList());
		if (!envEventsNotUsed.isEmpty())
			DashErrors.envEventsNotUsed(envEventsNotUsed);

		// we check that every state is either a default state 
		// or the destination of some transition
		// or an AND state
		// this is VERY conservative
		List<String> transDest = getAllTransNames().stream()
			.filter(i -> getDest(i)!=null)
			.map(i -> getDest(i).getName())
			.collect(Collectors.toList());
		List<String> statesNotEntered = st.getAllStateNames().stream()
			.filter(i -> !(st.isDefault(i) || st.isAnd(i) || st.isRoot(i) || transDest.contains(i)))
			.collect(Collectors.toList());
		if (!statesNotEntered.isEmpty())
			DashErrors.statesNotEntered(statesNotEntered);
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
