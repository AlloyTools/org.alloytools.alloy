package ca.uwaterloo.watform.parser;

import java.util.List;
import java.util.ArrayList;
import java.util.HashMap;

import static ca.uwaterloo.watform.core.DashUtilFcns.*;
import static ca.uwaterloo.watform.core.DashStrings.*;

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
}