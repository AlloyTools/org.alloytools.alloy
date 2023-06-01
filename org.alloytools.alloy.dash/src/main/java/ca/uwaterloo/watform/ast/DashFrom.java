package ca.uwaterloo.watform.ast;

import java.util.List;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;

import ca.uwaterloo.watform.core.DashStrings;
import ca.uwaterloo.watform.core.DashRef;

public class DashFrom extends Dash {

	public Expr src;
	public DashFrom(Pos pos,Expr d) {
		assert(d != null);
		this.pos = pos;
		this.src = d;
	}
	public String toString() {
		return DashStrings.fromName + " " + src.toString() + "\n";
	}

}
