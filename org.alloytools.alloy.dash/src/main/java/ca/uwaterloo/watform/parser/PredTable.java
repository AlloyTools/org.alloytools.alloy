package ca.uwaterloo.watform.parser;

import java.util.Set;
import java.util.List;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Collections;
import java.util.stream.Collectors;


import edu.mit.csail.sdg.ast.*;
import edu.mit.csail.sdg.alloy4.ConstList;

import static ca.uwaterloo.watform.alloyasthelper.ExprHelper.*;

import ca.uwaterloo.watform.core.*;
import static ca.uwaterloo.watform.core.DashUtilFcns.*;
import static ca.uwaterloo.watform.core.DashStrings.*;
import ca.uwaterloo.watform.core.DashRef;
import ca.uwaterloo.watform.dashtoalloy.Common;

import ca.uwaterloo.watform.parser.StateTable;
import ca.uwaterloo.watform.parser.VarTable;

public class PredTable {

	private HashMap<String,PredElement> predTable;

	public PredTable() {
		this.predTable = new LinkedHashMap<String,PredElement>();
	}

	public class PredElement {

		// this expression must be resolved in the context of the guard/action
		// it is used in
		// because otherwise we might have orphan parameter values
		// from the context where it is declared
		private Expr exp;

		public PredElement(
			Expr e) {
			this.exp = e;
		}
		public String toString() {
			String s = new String();
			s += "exp: "+exp.toString() + "\n";
			return s;
		}
	}

	public String toString() {
		String s = new String("PRED TABLE\n");
		for (String k:predTable.keySet()) {
			s += " ----- \n";
			s += k + "\n";
			s += predTable.get(k).toString();
		}
		return s;
	}	
	public Boolean addPred(String n, Expr e) {
		if (predTable.containsKey(n)) return false;
		else { predTable.put(n, new PredElement(e)); return true; }
	}
	public Expr getExp(String pfqn) {
		if (predTable.containsKey(pfqn)) return predTable.get(pfqn).exp;
		else { DashErrors.predDoesNotExist("getExp", pfqn); return null; }	
	}
	public boolean contains(String pfqn) {
		return predTable.containsKey(pfqn);
	}
	public List<String> getAllNames() {
		return new ArrayList<String>(predTable.keySet());
	}
}