package ca.uwaterloo.watform.ast;



import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;

import ca.uwaterloo.watform.core.DashStrings;

public class DashDo  extends Dash {
	public Expr action;

	public DashDo(Pos pos,Expr a) {
		this.pos = pos;
		this.action = a;

	}
	public String toString() {
		String s = new String();
		s += DashStrings.doName + " ";
		s += "{\n";
		s += action.toString() + "\n";
		s += "}\n";
		return s;
	}
}