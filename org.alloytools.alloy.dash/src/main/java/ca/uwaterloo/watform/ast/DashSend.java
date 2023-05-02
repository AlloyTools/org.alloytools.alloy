/* 
	This class is used only during parsing but is necessary because
	we do not know what order items of a transitions will be parsed in.
*/

package ca.uwaterloo.watform.ast;


import java.util.ArrayList;
import java.util.StringJoiner;

import ca.uwaterloo.watform.core.DashStrings;
import ca.uwaterloo.watform.core.DashRef;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;

// send P[x]/ev1
// send ev1
// send y.x.ev1

public class DashSend  extends Dash {

	//public DashRef ref;
	public Expr exp;

	/*
	public DashSend(Pos pos,DashRef r) {
		assert(r != null);
		this.pos = pos;
		this.ref = r;
		this.exp = null;
	}
	*/
	public DashSend(Pos pos,Expr e) {
		assert(e != null);
		this.pos = pos;
		this.exp = e;
		//this.ref = null;
	}
	public String toString() {
		//if (ref != null)
		//	return DashStrings.sendName + " " + ref.toString() + "\n";
		//else
			return DashStrings.sendName + " " + exp.toString() + "\n";
	}
	public Expr getExp() {
		return exp;
	}
}

