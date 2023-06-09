/* 
	These classes are used only during parsing because
	we do not know what order items within a state will be parsed in.
*/

package ca.uwaterloo.watform.ast;



import ca.uwaterloo.watform.core.DashStrings;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;

public class DashInit extends DashExpr {	

    public DashInit(Pos p, Expr i) {
        super(p,i);
    }
    public String toString() {
        return super.toString(DashStrings.initName);
    }
}
