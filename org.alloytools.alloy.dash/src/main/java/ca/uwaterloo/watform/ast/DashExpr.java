/* 
	These classes are used only during parsing because
	we do not know what order items within a state will be parsed in.
*/

package ca.uwaterloo.watform.ast;



import ca.uwaterloo.watform.core.DashStrings;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;

public abstract class DashExpr extends Dash {	

    public Expr exp;

    public DashExpr(Pos p, Expr e) {
        assert(e != null);
        this.pos = p;
        this.exp = e; 
    }
    public String toString(String name) {
        String s = new String();
        s += name + " {\n";
        s += exp.toString() + "\n";
        return s + "}\n";
    }
    public Expr getExp() {
        return exp;
    }
}
