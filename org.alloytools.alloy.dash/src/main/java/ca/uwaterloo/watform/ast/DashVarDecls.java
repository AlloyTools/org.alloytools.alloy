package ca.uwaterloo.watform.ast;

import java.util.List;
import java.util.StringJoiner;

import ca.uwaterloo.watform.core.DashStrings;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;

public class DashVarDecls extends Dash {
 

	private List<String> names;
	private Expr typ;
	private DashStrings.IntEnvKind kind;



	public DashVarDecls (Pos pos, List<String> n, Expr e, DashStrings.IntEnvKind k) {
		assert(n != null && e != null);
		this.pos = pos;
		this.names = n;
		this.typ = e;
		this.kind = k;
	}

	public String toString() {
		String s = new String("");
		if (kind == DashStrings.IntEnvKind.ENV) {
			s += DashStrings.envName + " ";
		}
		StringJoiner sj = new StringJoiner(",\n");
        names.forEach(n -> sj.add(n));
		return s + sj.toString() + ":" + typ.toString() + "\n";
	}
	public List<String> getNames() {
		return names;
	}
	public Expr getTyp() {
		return typ;
	}
	public DashStrings.IntEnvKind getKind() {
		return kind;
	}
}