package ca.uwaterloo.watform.ast;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;

import ca.uwaterloo.watform.core.DashStrings;

public class DashWhen  extends Dash {
	public Expr when;
	public DashWhen(Pos pos,Expr w) {
		this.pos = pos;
		this.when = w;
	}
	public String toString() {
		return DashStrings.whenName + " " + when.toString() + "\n";
	}
}