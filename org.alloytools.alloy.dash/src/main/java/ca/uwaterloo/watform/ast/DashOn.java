package ca.uwaterloo.watform.ast;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;

import ca.uwaterloo.watform.core.DashStrings;

public class DashOn extends Dash {
	public Expr ev;
	public DashOn(Pos pos,Expr e) {
		this.pos = pos;
		this.ev = e;
	}
	public String toString() {
		return DashStrings.onName + " " + ev + "\n";
	}
}