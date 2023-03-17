package ca.uwaterloo.watform.ast;

import java.util.List;
import java.util.StringJoiner;

import edu.mit.csail.sdg.alloy4.Pos;

import ca.uwaterloo.watform.core.DashStrings;

public class DashEventDecls extends Dash {



	private List<String> names;
	private DashStrings.IntEnvKind kind; 

	public DashEventDecls(Pos pos, List<String> n, DashStrings.IntEnvKind kind) {
		assert(n != null);
		this.pos = pos;
		this.names = n;
		this.kind = kind;
	}

	public String toString() {
		String s = new String("");
		if (kind == DashStrings.IntEnvKind.ENV) {
			s += DashStrings.envName + " ";
		}
		StringJoiner sj = new StringJoiner(",\n");
        names.forEach(n -> sj.add(n));
		s += DashStrings.eventName + " " + sj.toString() +"{ }\n";
		return s;
	}
}