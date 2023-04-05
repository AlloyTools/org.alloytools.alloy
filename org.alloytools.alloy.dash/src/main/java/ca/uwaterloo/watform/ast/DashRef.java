package ca.uwaterloo.watform.ast;

import java.util.List;
import java.util.ArrayList;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;

import ca.uwaterloo.watform.core.DashUtilFcns;

public class DashRef extends Dash {
	private String name;
	private List<Expr> paramValues;

	public DashRef(Pos p, String n, List<Expr> eList) {
		this.pos = p;
		this.name = n;
		assert(n != null);
		assert(!n.isEmpty());
		assert(eList != null);
		this.paramValues = eList;
	}

	public DashRef(String n, List<Expr> eList) {
		this.pos = Pos.UNKNOWN;
		this.name = n;
		this.paramValues = eList;
	}

	public String getName() {
		return name;
	}
	public List<Expr> getParamValues() {
		return paramValues;
	}
	public String toString() {
		String r = "";
		r += name + "[" + DashUtilFcns.strCommaList(paramValues) +"]";
		return r;
	}
	public static List<Expr> emptyParamValuesList() {
		return new ArrayList<Expr>();
	}
}