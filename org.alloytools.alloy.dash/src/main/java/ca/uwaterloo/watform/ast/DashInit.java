/* 
	These classes are used only during parsing because
	we do not know what order items within a state will be parsed in.
*/

package ca.uwaterloo.watform.ast;



import ca.uwaterloo.watform.core.DashStrings;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;

public class DashInit extends Dash {	

    public Expr init;

    public DashInit(Pos p, Expr i) {
        assert(i != null);
        this.pos = p;
        this.init = i;
    }
    public String toString() {
        String s = new String();
        s += DashStrings.initName + " {\n";
        s += init.toString() + "\n";
        return s + "}\n";
    }
}
