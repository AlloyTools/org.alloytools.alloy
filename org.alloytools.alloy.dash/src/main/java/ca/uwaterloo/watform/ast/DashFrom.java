package ca.uwaterloo.watform.ast;

import edu.mit.csail.sdg.alloy4.Pos;

import ca.uwaterloo.watform.core.DashStrings;

public class DashFrom extends Dash {
	public String src;
	public DashFrom(Pos pos,String f) {
		this.pos = pos;
		this.src = f;
	}
	public String toString() {
		return DashStrings.fromName + " " + src + "\n";
	}
}
