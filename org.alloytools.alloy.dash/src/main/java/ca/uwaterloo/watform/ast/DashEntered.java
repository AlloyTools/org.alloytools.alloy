package ca.uwaterloo.watform.ast;



import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;

import ca.uwaterloo.watform.core.DashStrings;

public class DashEntered extends DashExpr {


    public DashEntered(Pos p, Expr e) {
        super(p,e);
    }
 
    public String toString() {
        return super.toString(DashStrings.enterName);
    }
}