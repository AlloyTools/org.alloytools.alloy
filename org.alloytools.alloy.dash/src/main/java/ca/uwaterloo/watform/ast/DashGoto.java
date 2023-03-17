package ca.uwaterloo.watform.ast;

import edu.mit.csail.sdg.alloy4.Pos;

import ca.uwaterloo.watform.core.DashStrings;


public class DashGoto extends Dash {
	public String dest;
	public DashGoto(Pos pos,String g) {
		assert(g != null);
		this.pos = pos;
		this.dest = g;
	}
	public String toString() {
		return DashStrings.gotoName + " " + dest + "\n";
	}
}