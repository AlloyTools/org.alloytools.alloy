package ca.uwaterloo.watform.ast;

import java.util.List;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;

import ca.uwaterloo.watform.core.DashUtilFcns.*;
import ca.uwaterloo.watform.core.DashStrings;
import ca.uwaterloo.watform.core.DashRef;

public class DashGoto extends Dash {
	public Expr dest;
	public DashGoto(Pos pos,Expr d) {
		assert(d!=null);
		this.pos = pos;
		this.dest = d;
	}
	public String toString() {
		return DashStrings.gotoName + "  " +dest.toString() + "\n";
	}
}