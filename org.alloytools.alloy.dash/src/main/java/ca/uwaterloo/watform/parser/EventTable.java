package ca.uwaterloo.watform.parser;

import java.util.List;
import java.io.Serializable;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Collections;
import java.util.stream.Collectors;

import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprVar;

import static ca.uwaterloo.watform.core.DashUtilFcns.*;
import static ca.uwaterloo.watform.core.DashStrings.*;
import ca.uwaterloo.watform.core.DashErrors;
import ca.uwaterloo.watform.core.DashFQN;
import ca.uwaterloo.watform.core.DashRef;

import ca.uwaterloo.watform.alloyasthelper.ExprHelper;
import ca.uwaterloo.watform.dashtoalloy.Common;

public class EventTable implements Serializable {

	// stores Event Decls in a HashMap based on the event FQN

	private LinkedHashMap<String,EventElement> table;


	public class EventElement {
		private IntEnvKind kind;
		private List<String> params;
		private List<Integer> paramsIdx;

		public EventElement(
			IntEnvKind k,
			List<String> prms,
			List<Integer> prmsIdx) {
			assert(prms != null);
			this.kind = k;
			this.params = prms;
			this.paramsIdx = prmsIdx;
		}
		public String toString() {
			String s = new String();
			s += "kind: "+kind+"\n";
			s += "params: "+ NoneStringIfNeeded(params) +"\n";
			s += "paramsIdx: "+ NoneStringIfNeeded(paramsIdx) +"\n";
			return s;
		}
	}

	public EventTable() {
		this.table = new LinkedHashMap<String,EventElement>();

	}
	public String toString() {
		String s = new String("EVENT TABLE\n");
		for (String k:table.keySet()) {
			s += " ----- \n";
			s += k + "\n";
			s += table.get(k).toString();
		}
		return s;
	}	
	public Boolean add(String efqn, IntEnvKind k, List<String> prms, List<Integer> prmsIdx) {
		assert(prms!=null);
		if (table.containsKey(efqn)) return false;
		else if (hasPrime(efqn)) { DashErrors.nameShouldNotBePrimed(efqn); return false; }
		else { table.put(efqn, new EventElement(k,prms,prmsIdx)); return true; }
	}
	public void resolveAllEventTable() {

	}
	public boolean hasEvents() {
		return (!table.keySet().isEmpty() );
	}
	public boolean hasEvent(String e) {
		return table.containsKey(e);
	}
	public boolean hasEventsAti(int i) {
		for (String e: table.keySet()) {
			if (table.get(e).params.size() == i) return true;
		}
		return false;	
	}
	public boolean hasInternalEventsAti(int i) {
		for (String e: table.keySet()) {
			if (table.get(e).params.size() == i && table.get(e).kind == IntEnvKind.INT) return true;
		}
		return false;	
	}
	public boolean hasEnvironmentalEventsAti(int i) {
		for (String e: table.keySet()) {
			if (table.get(e).params.size() == i && table.get(e).kind == IntEnvKind.ENV) return true;
		}
		return false;	
	}
	public boolean hasInternalEvents() {
		for (String e: table.keySet()) {
			if (table.get(e).kind == IntEnvKind.INT) return true;
		}
		return false;
	}
	public boolean hasEnvironmentalEvents() {
		for (String e: table.keySet()) {
			if (table.get(e).kind == IntEnvKind.ENV) return true;
		}
		return false;
	}
	public List<String> getAllInternalEvents() {
		return table.keySet().stream()
			.filter(i -> table.get(i).kind == IntEnvKind.INT)
			.collect(Collectors.toList());	
	}
	public List<String> getAllEnvironmentalEvents() {
		return table.keySet().stream()
			.filter(i -> table.get(i).kind == IntEnvKind.ENV)
			.collect(Collectors.toList());	
	}
	public List<String> getAllEventNames() {
		return new ArrayList<String>(table.keySet());
	}
	public List<String> getParams(String efqn) {
		if (table.containsKey(efqn)) return table.get(efqn).params;
		else { DashErrors.eventTableEventNotFound("getParams", efqn); return null; }
	}
	public List<Integer> getParamsIdx(String efqn) {
		if (table.containsKey(efqn)) return table.get(efqn).paramsIdx;
		else { DashErrors.eventTableEventNotFound("getParamsIdx", efqn); return null; }
	}
	public boolean isEnvironmentalEvent(String efqn) {
		if (table.containsKey(efqn)) return (table.get(efqn).kind == IntEnvKind.ENV);
		else { DashErrors.eventTableEventNotFound("isEnvironmentalEvent", efqn); return false; }	
	}
	public boolean isInternalEvent(String efqn) {
		if (table.containsKey(efqn)) return (table.get(efqn).kind == IntEnvKind.INT);
		else { DashErrors.eventTableEventNotFound("isInternalEvent", efqn); return false; }	
	}
	public List<String> getEventsOfState(String sfqn) {
		// return all events declared in this state
		// will have the sfqn as a prefix
		return table.keySet().stream()
			.filter(i -> DashFQN.chopPrefixFromFQN(i).equals(sfqn))
			.collect(Collectors.toList());	
	}

}