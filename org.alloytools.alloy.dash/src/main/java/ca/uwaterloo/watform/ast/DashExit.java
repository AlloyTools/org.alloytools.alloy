package ca.uwaterloo.watform.ast;



import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;

public class DashExit {

    public Expr expr;
    public Pos  pos;

    public DashExit(Pos pos, Expr expr) {
        this.expr = expr;
        this.pos = pos;
    }

}
