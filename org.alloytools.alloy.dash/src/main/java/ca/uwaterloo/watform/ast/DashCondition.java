package ca.uwaterloo.watform.ast;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;

public class DashCondition {

    public Pos    pos;
    public String name;
    public Expr   expr;

    public DashCondition(Pos pos, String name, Expr expr) {
        this.pos = pos;
        this.name = name;
        this.expr = expr;
    }
}
