package ca.uwaterloo.watform.parser;

import java.util.List;
import java.util.ArrayList;
import java.util.HashMap;

import edu.mit.csail.sdg.ast.Expr;


import static ca.uwaterloo.watform.core.DashUtilFcns.*;
import static ca.uwaterloo.watform.core.DashStrings.*;

public class BufferTable {

	// stores Buffer Decls in a HashMap based on the buffer FQN

	private HashMap<String,BufferElement> table;


	public class BufferElement {
		private IntEnvKind kind;
		private List<String> params;
		private String element;

		public BufferElement(
			IntEnvKind k,
			List<String> prms,
			String e) {
			assert(prms != null);
			this.kind = k;
			this.params = prms;
			this.element = e;
		}
		public String toString() {
			String s = new String();
			s += "kind: "+kind+"\n";
			s += "params: "+ NoneStringIfNeeded(params) +"\n";
			s += "element: "+element.toString() + "\n";
			return s;
		}
	}

	public BufferTable() {
		this.table = new HashMap<String,BufferElement>();

	}
	public String toString() {
		String s = new String("BUFFER TABLE\n");
		for (String k:table.keySet()) {
			s += " ----- \n";
			s += k + "\n";
			s += table.get(k).toString();
		}
		return s;
	}	
	public Boolean add(String vfqn, IntEnvKind k, List<String> prms, String el) {
		assert(prms!=null);
		if (table.containsKey(vfqn)) return false;
		else { table.put(vfqn, new BufferElement(k,prms, el)); return true; }
	}
	public void resolveAllBufferTable() {
		// TODO
	}
}