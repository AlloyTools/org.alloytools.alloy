package ca.uwaterloo.watform.ast;

import java.util.List;
import java.util.StringJoiner;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;

import ca.uwaterloo.watform.core.DashStrings;

public class DashBufferDecls extends Dash {
    /**
     * The filename, line, and column position in the original Alloy model file
     * (cannot be null).
     */
 
	private List<String> names;
	private String element;
	private DashStrings.IntEnvKind kind;

	public DashBufferDecls(Pos pos, List<String> n, String element, DashStrings.IntEnvKind k) {
		assert (n != null && element != null);
		this.pos = pos;
		this.names = n;
		this.element = element;
		this.kind = k;
	}


	public String toString() {
		String s = new String("");
		if (kind == DashStrings.IntEnvKind.ENV) {
			s += DashStrings.envName + " ";
		}
		StringJoiner sj = new StringJoiner(",\n");
        names.forEach(n -> sj.add(n));
		s += sj.toString() + ":" + DashStrings.bufName + "[" + element + "]\n";
		return s;
	}
	public List<String> getNames() {
		return names;
	}
	public String getElement() {
		return element;
	}
	public DashStrings.IntEnvKind getKind() {
		return kind;
	}
}