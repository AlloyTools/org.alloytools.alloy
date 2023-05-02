package ca.uwaterloo.watform.parser;

import java.util.List;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Collections;
import java.util.stream.Collectors;

import static ca.uwaterloo.watform.core.DashUtilFcns.*;
import static ca.uwaterloo.watform.core.DashStrings.*;
import ca.uwaterloo.watform.core.DashErrors;
import ca.uwaterloo.watform.core.DashFQN;

public class EventTable {

	// stores Event Decls in a HashMap based on the event FQN

	private HashMap<String,EventElement> table;


	public class EventElement {
		private IntEnvKind kind;
		private List<String> params;

		public EventElement(
			IntEnvKind k,
			List<String> prms) {
			assert(prms != null);
			this.kind = k;
			this.params = prms;
		}
		public String toString() {
			String s = new String();
			s += "kind: "+kind+"\n";
			s += "params: "+ NoneStringIfNeeded(params) +"\n";
			return s;
		}
	}

	public EventTable() {
		this.table = new HashMap<String,EventElement>();

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
	public Boolean add(String efqn, IntEnvKind k, List<String> prms) {
		assert(prms!=null);
		if (table.containsKey(efqn)) return false;
		else { table.put(efqn, new EventElement(k,prms)); return true; }
	}
	public void resolveAllEventTable() {
		// TODO
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
	public List<String> getParams(String ev) {
		if (table.containsKey(ev)) return table.get(ev).params;
		else { DashErrors.eventTableGetParams(); return null; }
	}
	public List<String> allEventsOfState(String sfqn) {
		// return all events declared in this state
		// will have the sfqn as a prefix
		return table.keySet().stream()
			.filter(i -> DashFQN.chopPrefixFromFQN(i).equals(sfqn))
			.collect(Collectors.toList());	
	}
}