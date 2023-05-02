package ca.uwaterloo.watform.ast;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;

import ca.uwaterloo.watform.core.DashStrings;
import ca.uwaterloo.watform.core.DashRef;

public class DashOn extends Dash {
	//public DashRef ref;
	public Expr exp;
	/*
	public DashOn(Pos pos,DashRef r) {
		assert(r != null);
		this.pos = pos;
		this.ref = r;
		this.exp = null;
	}
	*/
	public DashOn(Pos pos, Expr e) {
		assert (e != null);
		this.pos = pos;
		this.exp = e;
		//this.ref = null;
	}
	public String toString() {
		//if (ref != null)
		//	return DashStrings.onName + " " + ref.toString() + "\n";
		//else
			return DashStrings.onName + " " + exp.toString() + "\n";
	}
	public Expr getExp() {
		return exp;
	}
}