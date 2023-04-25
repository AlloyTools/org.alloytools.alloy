package ca.uwaterloo.watform.parser;

import java.util.List;
import java.util.ArrayList;
import java.util.HashMap;

import edu.mit.csail.sdg.ast.Expr;


import static ca.uwaterloo.watform.core.DashUtilFcns.*;
import static ca.uwaterloo.watform.core.DashStrings.*;

public class VarTable {

	// stores Var Decls in a HashMap based on the event FQN

	private HashMap<String,VarElement> table;


	public class VarElement {
		private IntEnvKind kind;
		private List<String> params;
		private Expr typ;

		public VarElement(
			IntEnvKind k,
			List<String> prms,
			Expr t) {
			assert(prms != null);
			this.kind = k;
			this.params = prms;
			this.typ = t;
		}
		public String toString() {
			String s = new String();
			s += "kind: "+kind+"\n";
			s += "params: "+ NoneStringIfNeeded(params) +"\n";
			s += "typ: "+typ.toString() + "\n";
			return s;
		}
	}

	public VarTable() {
		this.table = new HashMap<String,VarElement>();

	}
	public String toString() {
		String s = new String("VAR TABLE\n");
		for (String k:table.keySet()) {
			s += " ----- \n";
			s += k + "\n";
			s += table.get(k).toString();
		}
		return s;
	}	
	public Boolean add(String vfqn, IntEnvKind k, List<String> prms, Expr t) {
		assert(prms!=null);
		if (table.containsKey(vfqn)) return false;
		else { table.put(vfqn, new VarElement(k,prms, t)); return true; }
	}
	public void resolveAllVarTable() {
		// TODO
	}
}