package ca.uwaterloo.watform.ast;

import java.util.List;
import java.util.StringJoiner;
import java.util.Collections;
import java.util.stream.Collectors;

import ca.uwaterloo.watform.core.*;

import ca.uwaterloo.watform.parser.StateTable;
import ca.uwaterloo.watform.parser.TransTable;

import edu.mit.csail.sdg.alloy4.Pos;

public class DashTrans extends Dash {
	String name;
	List<Object> items;

	public DashTrans(Pos p,String n, List<Object> i) {
		assert(n != null && i != null);
		this.pos = p;
		this.name = n;
		this.items = i;
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
	public void resolveAll(StateTable st, TransTable tt, List<String> params, List<String> ances) {
		String tfqn = DashFQN.fqn(ances,name);
		//System.out.println("Resolving trans "+tfqn);		

	}
}