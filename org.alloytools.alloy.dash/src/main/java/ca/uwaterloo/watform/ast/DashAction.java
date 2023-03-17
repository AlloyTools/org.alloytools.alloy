/* 
	These classes are used only during parsing because
	we do not know what order items within a state will be parsed in.
*/

package ca.uwaterloo.watform.ast;

import ca.uwaterloo.watform.core.DashStrings;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;

public class DashAction extends Dash {	

    public String name;
    public Expr expr;

    public DashAction(Pos p, String n, Expr e) {
        assert(n != null & e != null);
        this.pos = p;
        this.name = n;
        this.expr = e;
    }
    public String toString() {
        String s = new String();
        s += DashStrings.actionName + " " + name + " [\n";
        s += expr.toString() + "\n";
        return s + "] { }\n";
    }
}
