package ca.uwaterloo.watform.ast;

import java.util.List;
import java.util.StringJoiner;

import ca.uwaterloo.watform.core.DashStrings;

import edu.mit.csail.sdg.alloy4.Pos;

public class DashTrans extends Dash {
	String name;
	List<Object> items;

	public DashTrans(Pos pos,String name, List<Object> items) {
		this.pos = pos;
		this.name = name;
		this.items = items;
	}

	public String toString() {
		String s = new String("");
		if (items == null) {
			s += DashStrings.transName + " " + name + " { }\n";
		} else { 
		    s += DashStrings.transName + " " + name + "{\n";
			StringJoiner j = new StringJoiner("");
 			items.forEach(i -> j.add(i.toString()));
			s += j.toString() + "}\n";
		}
		return s;
	}

}