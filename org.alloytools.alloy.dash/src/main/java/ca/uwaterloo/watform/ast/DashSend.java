/* 
	This class is used only during parsing but is necessary because
	we do not know what order items of a transitions will be parsed in.
*/

package ca.uwaterloo.watform.ast;


import java.util.ArrayList;
import java.util.StringJoiner;

import ca.uwaterloo.watform.core.DashStrings;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;

// send P[x]/ev1
// send ev1
// send y.x.ev1

public class DashSend  extends Dash {

	public Expr eventExpr;
	public DashSend(Pos pos,Expr ev) {
		assert(ev != null);
		this.pos = pos;
		this.eventExpr = ev;
	}
	public String toString() {
		return DashStrings.sendName + " " + eventExpr.toString() + "\n";
	}
}

